-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:50:47.042873+00:00
-- url     : https://prove2.me/submissions/cf631171-71b7-45d6-93d5-113eaee0f4ff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical293
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37621 raw37621Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw37621 raw37621Labels = mixedMoment B raw37621step0 raw37621step0Labels := by
      have hz : ∀ j, raw37621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37621step0 = (fun i j => raw37621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37621step0 raw37621; decide +kernel
      have hl : raw37621step0Labels = raw37621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37621 raw37621Labels permutation346 hz
    mixedMoment B raw37621step0 raw37621step0Labels = mixedMoment B raw37621step1 raw37621step1Labels := by
      have ha : raw37621step1 = -raw37621step0 := by apply Matrix.ext; change ∀ i j, raw37621step1 i j = -(raw37621step0 i j); unfold raw37621step1 raw37621step0; decide +kernel
      have hl : raw37621step1Labels = raw37621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical37622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37622 raw37622Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw37622 raw37622Labels = mixedMoment B raw37622step0 raw37622step0Labels := by
      have hz : ∀ j, raw37622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37622step0 = (fun i j => raw37622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37622step0 raw37622; decide +kernel
      have hl : raw37622step0Labels = raw37622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37622 raw37622Labels permutation346 hz
    mixedMoment B raw37622step0 raw37622step0Labels = mixedMoment B raw37622step1 raw37622step1Labels := by
      have ha : raw37622step1 = -raw37622step0 := by apply Matrix.ext; change ∀ i j, raw37622step1 i j = -(raw37622step0 i j); unfold raw37622step1 raw37622step0; decide +kernel
      have hl : raw37622step1Labels = raw37622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical37623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37623 raw37623Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw37623 raw37623Labels = mixedMoment B raw37623step0 raw37623step0Labels := by
      have hz : ∀ j, raw37623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37623step0 = (fun i j => raw37623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37623step0 raw37623; decide +kernel
      have hl : raw37623step0Labels = raw37623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37623 raw37623Labels permutation346 hz
    mixedMoment B raw37623step0 raw37623step0Labels = mixedMoment B raw37623step1 raw37623step1Labels := by
      have ha : raw37623step1 = -raw37623step0 := by apply Matrix.ext; change ∀ i j, raw37623step1 i j = -(raw37623step0 i j); unfold raw37623step1 raw37623step0; decide +kernel
      have hl : raw37623step1Labels = raw37623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3273 node3273Labels := by rfl

theorem canonical37624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37624 raw37624Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw37624 raw37624Labels = mixedMoment B raw37624step0 raw37624step0Labels := by
      have ha : raw37624step0 = (fun i j => raw37624 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37624step0 raw37624; decide +kernel
      have hl : raw37624step0Labels = raw37624Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37624 raw37624Labels permutation160 permutation4
    mixedMoment B raw37624step0 raw37624step0Labels = mixedMoment B raw37624step1 raw37624step1Labels := by
      have ha : raw37624step1 = -raw37624step0 := by apply Matrix.ext; change ∀ i j, raw37624step1 i j = -(raw37624step0 i j); unfold raw37624step1 raw37624step0; decide +kernel
      have hl : raw37624step1Labels = raw37624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical37625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37625 raw37625Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw37625 raw37625Labels = mixedMoment B raw37625step0 raw37625step0Labels := by
      have hz : ∀ j, raw37625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37625step0 = (fun i j => raw37625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37625step0 raw37625; decide +kernel
      have hl : raw37625step0Labels = raw37625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37625 raw37625Labels permutation346 hz
    mixedMoment B raw37625step0 raw37625step0Labels = mixedMoment B raw37625step1 raw37625step1Labels := by
      have ha : raw37625step1 = (fun i j => raw37625step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37625step1 raw37625step0; decide +kernel
      have hl : raw37625step1Labels = raw37625step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37625step0 raw37625step0Labels permutation34 permutation4
    mixedMoment B raw37625step1 raw37625step1Labels = mixedMoment B raw37625step2 raw37625step2Labels := by
      have ha : raw37625step2 = -raw37625step1 := by apply Matrix.ext; change ∀ i j, raw37625step2 i j = -(raw37625step1 i j); unfold raw37625step2 raw37625step1; decide +kernel
      have hl : raw37625step2Labels = raw37625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical37626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37626 raw37626Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw37626 raw37626Labels = mixedMoment B raw37626step0 raw37626step0Labels := by
      have hz : ∀ j, raw37626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37626step0 = (fun i j => raw37626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37626step0 raw37626; decide +kernel
      have hl : raw37626step0Labels = raw37626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37626 raw37626Labels permutation346 hz
    mixedMoment B raw37626step0 raw37626step0Labels = mixedMoment B raw37626step1 raw37626step1Labels := by
      have ha : raw37626step1 = (fun i j => raw37626step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37626step1 raw37626step0; decide +kernel
      have hl : raw37626step1Labels = raw37626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37626step0 raw37626step0Labels permutation32 permutation4
    mixedMoment B raw37626step1 raw37626step1Labels = mixedMoment B raw37626step2 raw37626step2Labels := by
      have ha : raw37626step2 = -raw37626step1 := by apply Matrix.ext; change ∀ i j, raw37626step2 i j = -(raw37626step1 i j); unfold raw37626step2 raw37626step1; decide +kernel
      have hl : raw37626step2Labels = raw37626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical37627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37627 raw37627Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw37627 raw37627Labels = mixedMoment B raw37627step0 raw37627step0Labels := by
      have hz : ∀ j, raw37627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37627step0 = (fun i j => raw37627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37627step0 raw37627; decide +kernel
      have hl : raw37627step0Labels = raw37627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37627 raw37627Labels permutation346 hz
    mixedMoment B raw37627step0 raw37627step0Labels = mixedMoment B raw37627step1 raw37627step1Labels := by
      have ha : raw37627step1 = (fun i j => raw37627step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37627step1 raw37627step0; decide +kernel
      have hl : raw37627step1Labels = raw37627step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37627step0 raw37627step0Labels permutation145 permutation4
    _ = mixedMoment B node2184 node2184Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical294
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37647 raw37647Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw37647 raw37647Labels = mixedMoment B raw37647step0 raw37647step0Labels := by
      have hz : ∀ j, raw37647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37647step0 = (fun i j => raw37647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37647step0 raw37647; decide +kernel
      have hl : raw37647step0Labels = raw37647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37647 raw37647Labels permutation346 hz
    mixedMoment B raw37647step0 raw37647step0Labels = mixedMoment B raw37647step1 raw37647step1Labels := by
      have ha : raw37647step1 = -raw37647step0 := by apply Matrix.ext; change ∀ i j, raw37647step1 i j = -(raw37647step0 i j); unfold raw37647step1 raw37647step0; decide +kernel
      have hl : raw37647step1Labels = raw37647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical37648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37648 raw37648Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw37648 raw37648Labels = mixedMoment B raw37648step0 raw37648step0Labels := by
      have hz : ∀ j, raw37648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37648step0 = (fun i j => raw37648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37648step0 raw37648; decide +kernel
      have hl : raw37648step0Labels = raw37648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37648 raw37648Labels permutation346 hz
    mixedMoment B raw37648step0 raw37648step0Labels = mixedMoment B raw37648step1 raw37648step1Labels := by
      have ha : raw37648step1 = (fun i j => raw37648step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37648step1 raw37648step0; decide +kernel
      have hl : raw37648step1Labels = raw37648step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37648step0 raw37648step0Labels permutation36 permutation2
    mixedMoment B raw37648step1 raw37648step1Labels = mixedMoment B raw37648step2 raw37648step2Labels := by
      have ha : raw37648step2 = -raw37648step1 := by apply Matrix.ext; change ∀ i j, raw37648step2 i j = -(raw37648step1 i j); unfold raw37648step2 raw37648step1; decide +kernel
      have hl : raw37648step2Labels = raw37648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical37649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37649 raw37649Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw37649 raw37649Labels = mixedMoment B raw37649step0 raw37649step0Labels := by
      have hz : ∀ j, raw37649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37649step0 = (fun i j => raw37649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37649step0 raw37649; decide +kernel
      have hl : raw37649step0Labels = raw37649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37649 raw37649Labels permutation346 hz
    mixedMoment B raw37649step0 raw37649step0Labels = mixedMoment B raw37649step1 raw37649step1Labels := by
      have ha : raw37649step1 = (fun i j => raw37649step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37649step1 raw37649step0; decide +kernel
      have hl : raw37649step1Labels = raw37649step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37649step0 raw37649step0Labels permutation36 permutation2
    mixedMoment B raw37649step1 raw37649step1Labels = mixedMoment B raw37649step2 raw37649step2Labels := by
      have ha : raw37649step2 = -raw37649step1 := by apply Matrix.ext; change ∀ i j, raw37649step2 i j = -(raw37649step1 i j); unfold raw37649step2 raw37649step1; decide +kernel
      have hl : raw37649step2Labels = raw37649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3270 node3270Labels := by rfl

theorem canonical37650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37650 raw37650Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw37650 raw37650Labels = mixedMoment B raw37650step0 raw37650step0Labels := by
      have ha : raw37650step0 = (fun i j => raw37650 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37650step0 raw37650; decide +kernel
      have hl : raw37650step0Labels = raw37650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37650 raw37650Labels permutation160 permutation4
    mixedMoment B raw37650step0 raw37650step0Labels = mixedMoment B raw37650step1 raw37650step1Labels := by
      have ha : raw37650step1 = -raw37650step0 := by apply Matrix.ext; change ∀ i j, raw37650step1 i j = -(raw37650step0 i j); unfold raw37650step1 raw37650step0; decide +kernel
      have hl : raw37650step1Labels = raw37650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical37651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37651 raw37651Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw37651 raw37651Labels = mixedMoment B raw37651step0 raw37651step0Labels := by
      have hz : ∀ j, raw37651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37651step0 = (fun i j => raw37651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37651step0 raw37651; decide +kernel
      have hl : raw37651step0Labels = raw37651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37651 raw37651Labels permutation346 hz
    mixedMoment B raw37651step0 raw37651step0Labels = mixedMoment B raw37651step1 raw37651step1Labels := by
      have ha : raw37651step1 = (fun i j => raw37651step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37651step1 raw37651step0; decide +kernel
      have hl : raw37651step1Labels = raw37651step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37651step0 raw37651step0Labels permutation34 permutation4
    mixedMoment B raw37651step1 raw37651step1Labels = mixedMoment B raw37651step2 raw37651step2Labels := by
      have ha : raw37651step2 = -raw37651step1 := by apply Matrix.ext; change ∀ i j, raw37651step2 i j = -(raw37651step1 i j); unfold raw37651step2 raw37651step1; decide +kernel
      have hl : raw37651step2Labels = raw37651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3270 node3270Labels := by rfl

theorem canonical37652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37652 raw37652Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw37652 raw37652Labels = mixedMoment B raw37652step0 raw37652step0Labels := by
      have hz : ∀ j, raw37652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37652step0 = (fun i j => raw37652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37652step0 raw37652; decide +kernel
      have hl : raw37652step0Labels = raw37652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37652 raw37652Labels permutation346 hz
    mixedMoment B raw37652step0 raw37652step0Labels = mixedMoment B raw37652step1 raw37652step1Labels := by
      have ha : raw37652step1 = (fun i j => raw37652step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37652step1 raw37652step0; decide +kernel
      have hl : raw37652step1Labels = raw37652step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37652step0 raw37652step0Labels permutation32 permutation4
    mixedMoment B raw37652step1 raw37652step1Labels = mixedMoment B raw37652step2 raw37652step2Labels := by
      have ha : raw37652step2 = -raw37652step1 := by apply Matrix.ext; change ∀ i j, raw37652step2 i j = -(raw37652step1 i j); unfold raw37652step2 raw37652step1; decide +kernel
      have hl : raw37652step2Labels = raw37652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical37653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37653 raw37653Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw37653 raw37653Labels = mixedMoment B raw37653step0 raw37653step0Labels := by
      have hz : ∀ j, raw37653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37653step0 = (fun i j => raw37653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37653step0 raw37653; decide +kernel
      have hl : raw37653step0Labels = raw37653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37653 raw37653Labels permutation346 hz
    mixedMoment B raw37653step0 raw37653step0Labels = mixedMoment B raw37653step1 raw37653step1Labels := by
      have ha : raw37653step1 = (fun i j => raw37653step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37653step1 raw37653step0; decide +kernel
      have hl : raw37653step1Labels = raw37653step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37653step0 raw37653step0Labels permutation151 permutation4
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical37654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37654 raw37654Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw37654 raw37654Labels = mixedMoment B raw37654step0 raw37654step0Labels := by
      have hz : ∀ j, raw37654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37654step0 = (fun i j => raw37654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37654step0 raw37654; decide +kernel
      have hl : raw37654step0Labels = raw37654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37654 raw37654Labels permutation346 hz
    mixedMoment B raw37654step0 raw37654step0Labels = mixedMoment B raw37654step1 raw37654step1Labels := by
      have ha : raw37654step1 = -raw37654step0 := by apply Matrix.ext; change ∀ i j, raw37654step1 i j = -(raw37654step0 i j); unfold raw37654step1 raw37654step0; decide +kernel
      have hl : raw37654step1Labels = raw37654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1691 node1691Labels := by rfl

theorem canonical37655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37655 raw37655Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw37655 raw37655Labels = mixedMoment B raw37655step0 raw37655step0Labels := by
      have hz : ∀ j, raw37655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37655step0 = (fun i j => raw37655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37655step0 raw37655; decide +kernel
      have hl : raw37655step0Labels = raw37655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37655 raw37655Labels permutation346 hz
    mixedMoment B raw37655step0 raw37655step0Labels = mixedMoment B raw37655step1 raw37655step1Labels := by
      have ha : raw37655step1 = -raw37655step0 := by apply Matrix.ext; change ∀ i j, raw37655step1 i j = -(raw37655step0 i j); unfold raw37655step1 raw37655step0; decide +kernel
      have hl : raw37655step1Labels = raw37655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3274 node3274Labels := by rfl

theorem canonical37656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37656 raw37656Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw37656 raw37656Labels = mixedMoment B raw37656step0 raw37656step0Labels := by
      have ha : raw37656step0 = (fun i j => raw37656 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37656step0 raw37656; decide +kernel
      have hl : raw37656step0Labels = raw37656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37656 raw37656Labels permutation158 permutation4
    mixedMoment B raw37656step0 raw37656step0Labels = mixedMoment B raw37656step1 raw37656step1Labels := by
      have ha : raw37656step1 = -raw37656step0 := by apply Matrix.ext; change ∀ i j, raw37656step1 i j = -(raw37656step0 i j); unfold raw37656step1 raw37656step0; decide +kernel
      have hl : raw37656step1Labels = raw37656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical37657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37657 raw37657Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw37657 raw37657Labels = mixedMoment B raw37657step0 raw37657step0Labels := by
      have hz : ∀ j, raw37657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37657step0 = (fun i j => raw37657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37657step0 raw37657; decide +kernel
      have hl : raw37657step0Labels = raw37657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37657 raw37657Labels permutation346 hz
    mixedMoment B raw37657step0 raw37657step0Labels = mixedMoment B raw37657step1 raw37657step1Labels := by
      have ha : raw37657step1 = (fun i j => raw37657step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37657step1 raw37657step0; decide +kernel
      have hl : raw37657step1Labels = raw37657step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37657step0 raw37657step0Labels permutation32 permutation4
    mixedMoment B raw37657step1 raw37657step1Labels = mixedMoment B raw37657step2 raw37657step2Labels := by
      have ha : raw37657step2 = -raw37657step1 := by apply Matrix.ext; change ∀ i j, raw37657step2 i j = -(raw37657step1 i j); unfold raw37657step2 raw37657step1; decide +kernel
      have hl : raw37657step2Labels = raw37657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3274 node3274Labels := by rfl

theorem canonical37658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37658 raw37658Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw37658 raw37658Labels = mixedMoment B raw37658step0 raw37658step0Labels := by
      have hz : ∀ j, raw37658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37658step0 = (fun i j => raw37658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37658step0 raw37658; decide +kernel
      have hl : raw37658step0Labels = raw37658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37658 raw37658Labels permutation346 hz
    mixedMoment B raw37658step0 raw37658step0Labels = mixedMoment B raw37658step1 raw37658step1Labels := by
      have ha : raw37658step1 = (fun i j => raw37658step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37658step1 raw37658step0; decide +kernel
      have hl : raw37658step1Labels = raw37658step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37658step0 raw37658step0Labels permutation33 permutation4
    mixedMoment B raw37658step1 raw37658step1Labels = mixedMoment B raw37658step2 raw37658step2Labels := by
      have ha : raw37658step2 = -raw37658step1 := by apply Matrix.ext; change ∀ i j, raw37658step2 i j = -(raw37658step1 i j); unfold raw37658step2 raw37658step1; decide +kernel
      have hl : raw37658step2Labels = raw37658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical37665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37665 raw37665Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw37665 raw37665Labels = mixedMoment B raw37665step0 raw37665step0Labels := by
      have hz : ∀ j, raw37665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37665step0 = (fun i j => raw37665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37665step0 raw37665; decide +kernel
      have hl : raw37665step0Labels = raw37665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37665 raw37665Labels permutation434 hz
    mixedMoment B raw37665step0 raw37665step0Labels = mixedMoment B raw37665step1 raw37665step1Labels := by
      have hz : ∀ j, raw37665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37665step1 = (fun i j => raw37665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37665step1 raw37665step0; decide +kernel
      have hl : raw37665step1Labels = raw37665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37665step0 raw37665step0Labels permutation80 hz
    mixedMoment B raw37665step1 raw37665step1Labels = mixedMoment B raw37665step2 raw37665step2Labels := by
      have ha : raw37665step2 = (fun i j => raw37665step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37665step2 raw37665step1; decide +kernel
      have hl : raw37665step2Labels = raw37665step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37665step1 raw37665step1Labels permutation30 permutation2
    _ = mixedMoment B node2169 node2169Labels := by rfl

theorem canonical37666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37666 raw37666Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw37666 raw37666Labels = mixedMoment B raw37666step0 raw37666step0Labels := by
      have hz : ∀ j, raw37666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37666step0 = (fun i j => raw37666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37666step0 raw37666; decide +kernel
      have hl : raw37666step0Labels = raw37666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37666 raw37666Labels permutation434 hz
    mixedMoment B raw37666step0 raw37666step0Labels = mixedMoment B raw37666step1 raw37666step1Labels := by
      have hz : ∀ j, raw37666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37666step1 = (fun i j => raw37666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37666step1 raw37666step0; decide +kernel
      have hl : raw37666step1Labels = raw37666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37666step0 raw37666step0Labels permutation80 hz
    mixedMoment B raw37666step1 raw37666step1Labels = mixedMoment B raw37666step2 raw37666step2Labels := by
      have ha : raw37666step2 = (fun i j => raw37666step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37666step2 raw37666step1; decide +kernel
      have hl : raw37666step2Labels = raw37666step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37666step1 raw37666step1Labels permutation30 permutation2
    _ = mixedMoment B node2163 node2163Labels := by rfl

theorem canonical37667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37667 raw37667Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw37667 raw37667Labels = mixedMoment B raw37667step0 raw37667step0Labels := by
      have hz : ∀ j, raw37667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37667step0 = (fun i j => raw37667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37667step0 raw37667; decide +kernel
      have hl : raw37667step0Labels = raw37667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37667 raw37667Labels permutation434 hz
    mixedMoment B raw37667step0 raw37667step0Labels = mixedMoment B raw37667step1 raw37667step1Labels := by
      have ha : raw37667step1 = (fun i j => raw37667step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37667step1 raw37667step0; decide +kernel
      have hl : raw37667step1Labels = raw37667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37667step0 raw37667step0Labels permutation147 permutation2
    _ = mixedMoment B node2161 node2161Labels := by rfl

theorem canonical37668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37668 raw37668Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw37668 raw37668Labels = mixedMoment B raw37668step0 raw37668step0Labels := by
      have hz : ∀ j, raw37668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37668step0 = (fun i j => raw37668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37668step0 raw37668; decide +kernel
      have hl : raw37668step0Labels = raw37668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37668 raw37668Labels permutation346 hz
    mixedMoment B raw37668step0 raw37668step0Labels = mixedMoment B raw37668step1 raw37668step1Labels := by
      have ha : raw37668step1 = (fun i j => raw37668step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37668step1 raw37668step0; decide +kernel
      have hl : raw37668step1Labels = raw37668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37668step0 raw37668step0Labels permutation147 permutation2
    _ = mixedMoment B node2161 node2161Labels := by rfl

theorem canonical37669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37669 raw37669Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw37669 raw37669Labels = mixedMoment B raw37669step0 raw37669step0Labels := by
      have hz : ∀ j, raw37669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37669step0 = (fun i j => raw37669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37669step0 raw37669; decide +kernel
      have hl : raw37669step0Labels = raw37669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37669 raw37669Labels permutation434 hz
    mixedMoment B raw37669step0 raw37669step0Labels = mixedMoment B raw37669step1 raw37669step1Labels := by
      have hz : ∀ j, raw37669step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37669step1 = (fun i j => raw37669step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37669step1 raw37669step0; decide +kernel
      have hl : raw37669step1Labels = raw37669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37669step0 raw37669step0Labels permutation80 hz
    mixedMoment B raw37669step1 raw37669step1Labels = mixedMoment B raw37669step2 raw37669step2Labels := by
      have ha : raw37669step2 = (fun i j => raw37669step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37669step2 raw37669step1; decide +kernel
      have hl : raw37669step2Labels = raw37669step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37669step1 raw37669step1Labels permutation9 permutation4
    mixedMoment B raw37669step2 raw37669step2Labels = mixedMoment B raw37669step3 raw37669step3Labels := by
      have ha : raw37669step3 = -raw37669step2 := by apply Matrix.ext; change ∀ i j, raw37669step3 i j = -(raw37669step2 i j); unfold raw37669step3 raw37669step2; decide +kernel
      have hl : raw37669step3Labels = raw37669step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2163 node2163Labels := by rfl

theorem canonical37670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37670 raw37670Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw37670 raw37670Labels = mixedMoment B raw37670step0 raw37670step0Labels := by
      have hz : ∀ j, raw37670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37670step0 = (fun i j => raw37670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37670step0 raw37670; decide +kernel
      have hl : raw37670step0Labels = raw37670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37670 raw37670Labels permutation434 hz
    mixedMoment B raw37670step0 raw37670step0Labels = mixedMoment B raw37670step1 raw37670step1Labels := by
      have hz : ∀ j, raw37670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37670step1 = (fun i j => raw37670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37670step1 raw37670step0; decide +kernel
      have hl : raw37670step1Labels = raw37670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37670step0 raw37670step0Labels permutation80 hz
    mixedMoment B raw37670step1 raw37670step1Labels = mixedMoment B raw37670step2 raw37670step2Labels := by
      have ha : raw37670step2 = (fun i j => raw37670step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37670step2 raw37670step1; decide +kernel
      have hl : raw37670step2Labels = raw37670step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37670step1 raw37670step1Labels permutation9 permutation4
    mixedMoment B raw37670step2 raw37670step2Labels = mixedMoment B raw37670step3 raw37670step3Labels := by
      have ha : raw37670step3 = -raw37670step2 := by apply Matrix.ext; change ∀ i j, raw37670step3 i j = -(raw37670step2 i j); unfold raw37670step3 raw37670step2; decide +kernel
      have hl : raw37670step3Labels = raw37670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2169 node2169Labels := by rfl

theorem canonical37671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37671 raw37671Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw37671 raw37671Labels = mixedMoment B raw37671step0 raw37671step0Labels := by
      have hz : ∀ j, raw37671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37671step0 = (fun i j => raw37671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37671step0 raw37671; decide +kernel
      have hl : raw37671step0Labels = raw37671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37671 raw37671Labels permutation434 hz
    mixedMoment B raw37671step0 raw37671step0Labels = mixedMoment B raw37671step1 raw37671step1Labels := by
      have hz : ∀ j, raw37671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37671step1 = (fun i j => raw37671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37671step1 raw37671step0; decide +kernel
      have hl : raw37671step1Labels = raw37671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37671step0 raw37671step0Labels permutation80 hz
    mixedMoment B raw37671step1 raw37671step1Labels = mixedMoment B raw37671step2 raw37671step2Labels := by
      have ha : raw37671step2 = (fun i j => raw37671step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37671step2 raw37671step1; decide +kernel
      have hl : raw37671step2Labels = raw37671step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37671step1 raw37671step1Labels permutation31 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical37672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37672 raw37672Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw37672 raw37672Labels = mixedMoment B raw37672step0 raw37672step0Labels := by
      have hz : ∀ j, raw37672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37672step0 = (fun i j => raw37672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37672step0 raw37672; decide +kernel
      have hl : raw37672step0Labels = raw37672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37672 raw37672Labels permutation434 hz
    mixedMoment B raw37672step0 raw37672step0Labels = mixedMoment B raw37672step1 raw37672step1Labels := by
      have hz : ∀ j, raw37672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37672step1 = (fun i j => raw37672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37672step1 raw37672step0; decide +kernel
      have hl : raw37672step1Labels = raw37672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37672step0 raw37672step0Labels permutation80 hz
    mixedMoment B raw37672step1 raw37672step1Labels = mixedMoment B raw37672step2 raw37672step2Labels := by
      have ha : raw37672step2 = (fun i j => raw37672step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37672step2 raw37672step1; decide +kernel
      have hl : raw37672step2Labels = raw37672step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37672step1 raw37672step1Labels permutation31 permutation4
    _ = mixedMoment B node3596 node3596Labels := by rfl

theorem canonical37673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37673 raw37673Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw37673 raw37673Labels = mixedMoment B raw37673step0 raw37673step0Labels := by
      have hz : ∀ j, raw37673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37673step0 = (fun i j => raw37673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37673step0 raw37673; decide +kernel
      have hl : raw37673step0Labels = raw37673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37673 raw37673Labels permutation434 hz
    mixedMoment B raw37673step0 raw37673step0Labels = mixedMoment B raw37673step1 raw37673step1Labels := by
      have hz : ∀ j, raw37673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37673step1 = (fun i j => raw37673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37673step1 raw37673step0; decide +kernel
      have hl : raw37673step1Labels = raw37673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37673step0 raw37673step0Labels permutation80 hz
    mixedMoment B raw37673step1 raw37673step1Labels = mixedMoment B raw37673step2 raw37673step2Labels := by
      have ha : raw37673step2 = (fun i j => raw37673step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37673step2 raw37673step1; decide +kernel
      have hl : raw37673step2Labels = raw37673step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37673step1 raw37673step1Labels permutation10 permutation4
    mixedMoment B raw37673step2 raw37673step2Labels = mixedMoment B raw37673step3 raw37673step3Labels := by
      have ha : raw37673step3 = -raw37673step2 := by apply Matrix.ext; change ∀ i j, raw37673step3 i j = -(raw37673step2 i j); unfold raw37673step3 raw37673step2; decide +kernel
      have hl : raw37673step3Labels = raw37673step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2273 node2273Labels := by rfl

theorem canonical37674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37674 raw37674Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw37674 raw37674Labels = mixedMoment B raw37674step0 raw37674step0Labels := by
      have hz : ∀ j, raw37674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37674step0 = (fun i j => raw37674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37674step0 raw37674; decide +kernel
      have hl : raw37674step0Labels = raw37674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37674 raw37674Labels permutation434 hz
    mixedMoment B raw37674step0 raw37674step0Labels = mixedMoment B raw37674step1 raw37674step1Labels := by
      have ha : raw37674step1 = (fun i j => raw37674step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37674step1 raw37674step0; decide +kernel
      have hl : raw37674step1Labels = raw37674step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37674step0 raw37674step0Labels permutation34 permutation4
    mixedMoment B raw37674step1 raw37674step1Labels = mixedMoment B raw37674step2 raw37674step2Labels := by
      have ha : raw37674step2 = -raw37674step1 := by apply Matrix.ext; change ∀ i j, raw37674step2 i j = -(raw37674step1 i j); unfold raw37674step2 raw37674step1; decide +kernel
      have hl : raw37674step2Labels = raw37674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical37675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37675 raw37675Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw37675 raw37675Labels = mixedMoment B raw37675step0 raw37675step0Labels := by
      have hz : ∀ j, raw37675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37675step0 = (fun i j => raw37675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37675step0 raw37675; decide +kernel
      have hl : raw37675step0Labels = raw37675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37675 raw37675Labels permutation346 hz
    mixedMoment B raw37675step0 raw37675step0Labels = mixedMoment B raw37675step1 raw37675step1Labels := by
      have ha : raw37675step1 = (fun i j => raw37675step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37675step1 raw37675step0; decide +kernel
      have hl : raw37675step1Labels = raw37675step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37675step0 raw37675step0Labels permutation34 permutation4
    mixedMoment B raw37675step1 raw37675step1Labels = mixedMoment B raw37675step2 raw37675step2Labels := by
      have ha : raw37675step2 = -raw37675step1 := by apply Matrix.ext; change ∀ i j, raw37675step2 i j = -(raw37675step1 i j); unfold raw37675step2 raw37675step1; decide +kernel
      have hl : raw37675step2Labels = raw37675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical37676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37676 raw37676Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw37676 raw37676Labels = mixedMoment B raw37676step0 raw37676step0Labels := by
      have hz : ∀ j, raw37676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37676step0 = (fun i j => raw37676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37676step0 raw37676; decide +kernel
      have hl : raw37676step0Labels = raw37676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37676 raw37676Labels permutation434 hz
    mixedMoment B raw37676step0 raw37676step0Labels = mixedMoment B raw37676step1 raw37676step1Labels := by
      have hz : ∀ j, raw37676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37676step1 = (fun i j => raw37676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37676step1 raw37676step0; decide +kernel
      have hl : raw37676step1Labels = raw37676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37676step0 raw37676step0Labels permutation80 hz
    mixedMoment B raw37676step1 raw37676step1Labels = mixedMoment B raw37676step2 raw37676step2Labels := by
      have ha : raw37676step2 = (fun i j => raw37676step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37676step2 raw37676step1; decide +kernel
      have hl : raw37676step2Labels = raw37676step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37676step1 raw37676step1Labels permutation8 permutation4
    mixedMoment B raw37676step2 raw37676step2Labels = mixedMoment B raw37676step3 raw37676step3Labels := by
      have ha : raw37676step3 = -raw37676step2 := by apply Matrix.ext; change ∀ i j, raw37676step3 i j = -(raw37676step2 i j); unfold raw37676step3 raw37676step2; decide +kernel
      have hl : raw37676step3Labels = raw37676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical37677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37677 raw37677Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw37677 raw37677Labels = mixedMoment B raw37677step0 raw37677step0Labels := by
      have hz : ∀ j, raw37677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37677step0 = (fun i j => raw37677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37677step0 raw37677; decide +kernel
      have hl : raw37677step0Labels = raw37677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37677 raw37677Labels permutation434 hz
    mixedMoment B raw37677step0 raw37677step0Labels = mixedMoment B raw37677step1 raw37677step1Labels := by
      have hz : ∀ j, raw37677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37677step1 = (fun i j => raw37677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37677step1 raw37677step0; decide +kernel
      have hl : raw37677step1Labels = raw37677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37677step0 raw37677step0Labels permutation80 hz
    mixedMoment B raw37677step1 raw37677step1Labels = mixedMoment B raw37677step2 raw37677step2Labels := by
      have ha : raw37677step2 = (fun i j => raw37677step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37677step2 raw37677step1; decide +kernel
      have hl : raw37677step2Labels = raw37677step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37677step1 raw37677step1Labels permutation31 permutation4
    _ = mixedMoment B node2159 node2159Labels := by rfl

theorem canonical37678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37678 raw37678Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37678 raw37678Labels = mixedMoment B raw37678step0 raw37678step0Labels := by
      have hz : ∀ j, raw37678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37678step0 = (fun i j => raw37678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37678step0 raw37678; decide +kernel
      have hl : raw37678step0Labels = raw37678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37678 raw37678Labels permutation434 hz
    mixedMoment B raw37678step0 raw37678step0Labels = mixedMoment B raw37678step1 raw37678step1Labels := by
      have hz : ∀ j, raw37678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37678step1 = (fun i j => raw37678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37678step1 raw37678step0; decide +kernel
      have hl : raw37678step1Labels = raw37678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37678step0 raw37678step0Labels permutation80 hz
    mixedMoment B raw37678step1 raw37678step1Labels = mixedMoment B raw37678step2 raw37678step2Labels := by
      have ha : raw37678step2 = (fun i j => raw37678step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37678step2 raw37678step1; decide +kernel
      have hl : raw37678step2Labels = raw37678step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37678step1 raw37678step1Labels permutation30 permutation2
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical37679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37679 raw37679Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw37679 raw37679Labels = mixedMoment B raw37679step0 raw37679step0Labels := by
      have hz : ∀ j, raw37679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37679step0 = (fun i j => raw37679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37679step0 raw37679; decide +kernel
      have hl : raw37679step0Labels = raw37679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37679 raw37679Labels permutation434 hz
    mixedMoment B raw37679step0 raw37679step0Labels = mixedMoment B raw37679step1 raw37679step1Labels := by
      have hz : ∀ j, raw37679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37679step1 = (fun i j => raw37679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37679step1 raw37679step0; decide +kernel
      have hl : raw37679step1Labels = raw37679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37679step0 raw37679step0Labels permutation80 hz
    mixedMoment B raw37679step1 raw37679step1Labels = mixedMoment B raw37679step2 raw37679step2Labels := by
      have ha : raw37679step2 = (fun i j => raw37679step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37679step2 raw37679step1; decide +kernel
      have hl : raw37679step2Labels = raw37679step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37679step1 raw37679step1Labels permutation8 permutation4
    mixedMoment B raw37679step2 raw37679step2Labels = mixedMoment B raw37679step3 raw37679step3Labels := by
      have ha : raw37679step3 = -raw37679step2 := by apply Matrix.ext; change ∀ i j, raw37679step3 i j = -(raw37679step2 i j); unfold raw37679step3 raw37679step2; decide +kernel
      have hl : raw37679step3Labels = raw37679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical37680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37680 raw37680Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw37680 raw37680Labels = mixedMoment B raw37680step0 raw37680step0Labels := by
      have hz : ∀ j, raw37680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37680step0 = (fun i j => raw37680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37680step0 raw37680; decide +kernel
      have hl : raw37680step0Labels = raw37680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37680 raw37680Labels permutation434 hz
    mixedMoment B raw37680step0 raw37680step0Labels = mixedMoment B raw37680step1 raw37680step1Labels := by
      have ha : raw37680step1 = (fun i j => raw37680step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37680step1 raw37680step0; decide +kernel
      have hl : raw37680step1Labels = raw37680step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37680step0 raw37680step0Labels permutation32 permutation4
    mixedMoment B raw37680step1 raw37680step1Labels = mixedMoment B raw37680step2 raw37680step2Labels := by
      have ha : raw37680step2 = -raw37680step1 := by apply Matrix.ext; change ∀ i j, raw37680step2 i j = -(raw37680step1 i j); unfold raw37680step2 raw37680step1; decide +kernel
      have hl : raw37680step2Labels = raw37680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical37681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37681 raw37681Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw37681 raw37681Labels = mixedMoment B raw37681step0 raw37681step0Labels := by
      have hz : ∀ j, raw37681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37681step0 = (fun i j => raw37681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37681step0 raw37681; decide +kernel
      have hl : raw37681step0Labels = raw37681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37681 raw37681Labels permutation346 hz
    mixedMoment B raw37681step0 raw37681step0Labels = mixedMoment B raw37681step1 raw37681step1Labels := by
      have ha : raw37681step1 = (fun i j => raw37681step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37681step1 raw37681step0; decide +kernel
      have hl : raw37681step1Labels = raw37681step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37681step0 raw37681step0Labels permutation32 permutation4
    mixedMoment B raw37681step1 raw37681step1Labels = mixedMoment B raw37681step2 raw37681step2Labels := by
      have ha : raw37681step2 = -raw37681step1 := by apply Matrix.ext; change ∀ i j, raw37681step2 i j = -(raw37681step1 i j); unfold raw37681step2 raw37681step1; decide +kernel
      have hl : raw37681step2Labels = raw37681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical37682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37682 raw37682Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37682 raw37682Labels = mixedMoment B raw37682step0 raw37682step0Labels := by
      have hz : ∀ j, raw37682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37682step0 = (fun i j => raw37682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37682step0 raw37682; decide +kernel
      have hl : raw37682step0Labels = raw37682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37682 raw37682Labels permutation434 hz
    mixedMoment B raw37682step0 raw37682step0Labels = mixedMoment B raw37682step1 raw37682step1Labels := by
      have hz : ∀ j, raw37682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37682step1 = (fun i j => raw37682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37682step1 raw37682step0; decide +kernel
      have hl : raw37682step1Labels = raw37682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37682step0 raw37682step0Labels permutation80 hz
    mixedMoment B raw37682step1 raw37682step1Labels = mixedMoment B raw37682step2 raw37682step2Labels := by
      have ha : raw37682step2 = (fun i j => raw37682step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37682step2 raw37682step1; decide +kernel
      have hl : raw37682step2Labels = raw37682step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37682step1 raw37682step1Labels permutation9 permutation2
    mixedMoment B raw37682step2 raw37682step2Labels = mixedMoment B raw37682step3 raw37682step3Labels := by
      have ha : raw37682step3 = -raw37682step2 := by apply Matrix.ext; change ∀ i j, raw37682step3 i j = -(raw37682step2 i j); unfold raw37682step3 raw37682step2; decide +kernel
      have hl : raw37682step3Labels = raw37682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical37683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37683 raw37683Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw37683 raw37683Labels = mixedMoment B raw37683step0 raw37683step0Labels := by
      have hz : ∀ j, raw37683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37683step0 = (fun i j => raw37683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37683step0 raw37683; decide +kernel
      have hl : raw37683step0Labels = raw37683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37683 raw37683Labels permutation434 hz
    mixedMoment B raw37683step0 raw37683step0Labels = mixedMoment B raw37683step1 raw37683step1Labels := by
      have ha : raw37683step1 = (fun i j => raw37683step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37683step1 raw37683step0; decide +kernel
      have hl : raw37683step1Labels = raw37683step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37683step0 raw37683step0Labels permutation34 permutation4
    mixedMoment B raw37683step1 raw37683step1Labels = mixedMoment B raw37683step2 raw37683step2Labels := by
      have ha : raw37683step2 = -raw37683step1 := by apply Matrix.ext; change ∀ i j, raw37683step2 i j = -(raw37683step1 i j); unfold raw37683step2 raw37683step1; decide +kernel
      have hl : raw37683step2Labels = raw37683step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical37684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37684 raw37684Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw37684 raw37684Labels = mixedMoment B raw37684step0 raw37684step0Labels := by
      have hz : ∀ j, raw37684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37684step0 = (fun i j => raw37684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37684step0 raw37684; decide +kernel
      have hl : raw37684step0Labels = raw37684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37684 raw37684Labels permutation346 hz
    mixedMoment B raw37684step0 raw37684step0Labels = mixedMoment B raw37684step1 raw37684step1Labels := by
      have ha : raw37684step1 = (fun i j => raw37684step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37684step1 raw37684step0; decide +kernel
      have hl : raw37684step1Labels = raw37684step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37684step0 raw37684step0Labels permutation34 permutation4
    mixedMoment B raw37684step1 raw37684step1Labels = mixedMoment B raw37684step2 raw37684step2Labels := by
      have ha : raw37684step2 = -raw37684step1 := by apply Matrix.ext; change ∀ i j, raw37684step2 i j = -(raw37684step1 i j); unfold raw37684step2 raw37684step1; decide +kernel
      have hl : raw37684step2Labels = raw37684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical37685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37685 raw37685Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw37685 raw37685Labels = mixedMoment B raw37685step0 raw37685step0Labels := by
      have hz : ∀ j, raw37685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37685step0 = (fun i j => raw37685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37685step0 raw37685; decide +kernel
      have hl : raw37685step0Labels = raw37685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37685 raw37685Labels permutation434 hz
    mixedMoment B raw37685step0 raw37685step0Labels = mixedMoment B raw37685step1 raw37685step1Labels := by
      have hz : ∀ j, raw37685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37685step1 = (fun i j => raw37685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37685step1 raw37685step0; decide +kernel
      have hl : raw37685step1Labels = raw37685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37685step0 raw37685step0Labels permutation80 hz
    mixedMoment B raw37685step1 raw37685step1Labels = mixedMoment B raw37685step2 raw37685step2Labels := by
      have ha : raw37685step2 = (fun i j => raw37685step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37685step2 raw37685step1; decide +kernel
      have hl : raw37685step2Labels = raw37685step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37685step1 raw37685step1Labels permutation31 permutation4
    _ = mixedMoment B node3422 node3422Labels := by rfl

theorem canonical37686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37686 raw37686Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw37686 raw37686Labels = mixedMoment B raw37686step0 raw37686step0Labels := by
      have hz : ∀ j, raw37686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37686step0 = (fun i j => raw37686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37686step0 raw37686; decide +kernel
      have hl : raw37686step0Labels = raw37686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37686 raw37686Labels permutation434 hz
    mixedMoment B raw37686step0 raw37686step0Labels = mixedMoment B raw37686step1 raw37686step1Labels := by
      have hz : ∀ j, raw37686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37686step1 = (fun i j => raw37686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37686step1 raw37686step0; decide +kernel
      have hl : raw37686step1Labels = raw37686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37686step0 raw37686step0Labels permutation80 hz
    mixedMoment B raw37686step1 raw37686step1Labels = mixedMoment B raw37686step2 raw37686step2Labels := by
      have ha : raw37686step2 = (fun i j => raw37686step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37686step2 raw37686step1; decide +kernel
      have hl : raw37686step2Labels = raw37686step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37686step1 raw37686step1Labels permutation31 permutation4
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical37687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37687 raw37687Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw37687 raw37687Labels = mixedMoment B raw37687step0 raw37687step0Labels := by
      have hz : ∀ j, raw37687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37687step0 = (fun i j => raw37687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37687step0 raw37687; decide +kernel
      have hl : raw37687step0Labels = raw37687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37687 raw37687Labels permutation434 hz
    mixedMoment B raw37687step0 raw37687step0Labels = mixedMoment B raw37687step1 raw37687step1Labels := by
      have hz : ∀ j, raw37687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37687step1 = (fun i j => raw37687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37687step1 raw37687step0; decide +kernel
      have hl : raw37687step1Labels = raw37687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37687step0 raw37687step0Labels permutation80 hz
    mixedMoment B raw37687step1 raw37687step1Labels = mixedMoment B raw37687step2 raw37687step2Labels := by
      have ha : raw37687step2 = (fun i j => raw37687step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37687step2 raw37687step1; decide +kernel
      have hl : raw37687step2Labels = raw37687step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37687step1 raw37687step1Labels permutation31 permutation2
    _ = mixedMoment B node3422 node3422Labels := by rfl

theorem canonical37688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37688 raw37688Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw37688 raw37688Labels = mixedMoment B raw37688step0 raw37688step0Labels := by
      have hz : ∀ j, raw37688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37688step0 = (fun i j => raw37688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37688step0 raw37688; decide +kernel
      have hl : raw37688step0Labels = raw37688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37688 raw37688Labels permutation434 hz
    mixedMoment B raw37688step0 raw37688step0Labels = mixedMoment B raw37688step1 raw37688step1Labels := by
      have ha : raw37688step1 = (fun i j => raw37688step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37688step1 raw37688step0; decide +kernel
      have hl : raw37688step1Labels = raw37688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37688step0 raw37688step0Labels permutation151 permutation2
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical37689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37689 raw37689Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw37689 raw37689Labels = mixedMoment B raw37689step0 raw37689step0Labels := by
      have hz : ∀ j, raw37689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37689step0 = (fun i j => raw37689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37689step0 raw37689; decide +kernel
      have hl : raw37689step0Labels = raw37689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37689 raw37689Labels permutation346 hz
    mixedMoment B raw37689step0 raw37689step0Labels = mixedMoment B raw37689step1 raw37689step1Labels := by
      have ha : raw37689step1 = (fun i j => raw37689step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37689step1 raw37689step0; decide +kernel
      have hl : raw37689step1Labels = raw37689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37689step0 raw37689step0Labels permutation151 permutation2
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical37690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37690 raw37690Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37690 raw37690Labels = mixedMoment B raw37690step0 raw37690step0Labels := by
      have hz : ∀ j, raw37690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37690step0 = (fun i j => raw37690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37690step0 raw37690; decide +kernel
      have hl : raw37690step0Labels = raw37690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37690 raw37690Labels permutation434 hz
    mixedMoment B raw37690step0 raw37690step0Labels = mixedMoment B raw37690step1 raw37690step1Labels := by
      have hz : ∀ j, raw37690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37690step1 = (fun i j => raw37690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37690step1 raw37690step0; decide +kernel
      have hl : raw37690step1Labels = raw37690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37690step0 raw37690step0Labels permutation80 hz
    mixedMoment B raw37690step1 raw37690step1Labels = mixedMoment B raw37690step2 raw37690step2Labels := by
      have ha : raw37690step2 = (fun i j => raw37690step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37690step2 raw37690step1; decide +kernel
      have hl : raw37690step2Labels = raw37690step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37690step1 raw37690step1Labels permutation9 permutation4
    mixedMoment B raw37690step2 raw37690step2Labels = mixedMoment B raw37690step3 raw37690step3Labels := by
      have ha : raw37690step3 = -raw37690step2 := by apply Matrix.ext; change ∀ i j, raw37690step3 i j = -(raw37690step2 i j); unfold raw37690step3 raw37690step2; decide +kernel
      have hl : raw37690step3Labels = raw37690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical37691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37691 raw37691Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw37691 raw37691Labels = mixedMoment B raw37691step0 raw37691step0Labels := by
      have hz : ∀ j, raw37691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37691step0 = (fun i j => raw37691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37691step0 raw37691; decide +kernel
      have hl : raw37691step0Labels = raw37691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37691 raw37691Labels permutation434 hz
    mixedMoment B raw37691step0 raw37691step0Labels = mixedMoment B raw37691step1 raw37691step1Labels := by
      have ha : raw37691step1 = (fun i j => raw37691step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37691step1 raw37691step0; decide +kernel
      have hl : raw37691step1Labels = raw37691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37691step0 raw37691step0Labels permutation144 permutation2
    _ = mixedMoment B node3512 node3512Labels := by rfl

theorem canonical37692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37692 raw37692Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw37692 raw37692Labels = mixedMoment B raw37692step0 raw37692step0Labels := by
      have hz : ∀ j, raw37692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37692step0 = (fun i j => raw37692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37692step0 raw37692; decide +kernel
      have hl : raw37692step0Labels = raw37692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37692 raw37692Labels permutation346 hz
    mixedMoment B raw37692step0 raw37692step0Labels = mixedMoment B raw37692step1 raw37692step1Labels := by
      have ha : raw37692step1 = (fun i j => raw37692step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37692step1 raw37692step0; decide +kernel
      have hl : raw37692step1Labels = raw37692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37692step0 raw37692step0Labels permutation144 permutation2
    _ = mixedMoment B node3512 node3512Labels := by rfl

theorem canonical37714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37714 raw37714Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw37714 raw37714Labels = mixedMoment B raw37714step0 raw37714step0Labels := by
      have hz : ∀ j, raw37714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37714step0 = (fun i j => raw37714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37714step0 raw37714; decide +kernel
      have hl : raw37714step0Labels = raw37714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37714 raw37714Labels permutation346 hz
    mixedMoment B raw37714step0 raw37714step0Labels = mixedMoment B raw37714step1 raw37714step1Labels := by
      have ha : raw37714step1 = (fun i j => raw37714step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37714step1 raw37714step0; decide +kernel
      have hl : raw37714step1Labels = raw37714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37714step0 raw37714step0Labels permutation144 permutation2
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical37715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37715 raw37715Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw37715 raw37715Labels = mixedMoment B raw37715step0 raw37715step0Labels := by
      have hz : ∀ j, raw37715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37715step0 = (fun i j => raw37715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37715step0 raw37715; decide +kernel
      have hl : raw37715step0Labels = raw37715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37715 raw37715Labels permutation346 hz
    mixedMoment B raw37715step0 raw37715step0Labels = mixedMoment B raw37715step1 raw37715step1Labels := by
      have ha : raw37715step1 = (fun i j => raw37715step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37715step1 raw37715step0; decide +kernel
      have hl : raw37715step1Labels = raw37715step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37715step0 raw37715step0Labels permutation38 permutation4
    mixedMoment B raw37715step1 raw37715step1Labels = mixedMoment B raw37715step2 raw37715step2Labels := by
      have ha : raw37715step2 = -raw37715step1 := by apply Matrix.ext; change ∀ i j, raw37715step2 i j = -(raw37715step1 i j); unfold raw37715step2 raw37715step1; decide +kernel
      have hl : raw37715step2Labels = raw37715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical37716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37716 raw37716Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw37716 raw37716Labels = mixedMoment B raw37716step0 raw37716step0Labels := by
      have ha : raw37716step0 = (fun i j => raw37716 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37716step0 raw37716; decide +kernel
      have hl : raw37716step0Labels = raw37716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37716 raw37716Labels permutation158 permutation4
    mixedMoment B raw37716step0 raw37716step0Labels = mixedMoment B raw37716step1 raw37716step1Labels := by
      have ha : raw37716step1 = -raw37716step0 := by apply Matrix.ext; change ∀ i j, raw37716step1 i j = -(raw37716step0 i j); unfold raw37716step1 raw37716step0; decide +kernel
      have hl : raw37716step1Labels = raw37716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical37717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37717 raw37717Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw37717 raw37717Labels = mixedMoment B raw37717step0 raw37717step0Labels := by
      have hz : ∀ j, raw37717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37717step0 = (fun i j => raw37717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37717step0 raw37717; decide +kernel
      have hl : raw37717step0Labels = raw37717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37717 raw37717Labels permutation346 hz
    mixedMoment B raw37717step0 raw37717step0Labels = mixedMoment B raw37717step1 raw37717step1Labels := by
      have ha : raw37717step1 = (fun i j => raw37717step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37717step1 raw37717step0; decide +kernel
      have hl : raw37717step1Labels = raw37717step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37717step0 raw37717step0Labels permutation32 permutation4
    mixedMoment B raw37717step1 raw37717step1Labels = mixedMoment B raw37717step2 raw37717step2Labels := by
      have ha : raw37717step2 = -raw37717step1 := by apply Matrix.ext; change ∀ i j, raw37717step2 i j = -(raw37717step1 i j); unfold raw37717step2 raw37717step1; decide +kernel
      have hl : raw37717step2Labels = raw37717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2165 node2165Labels := by rfl

theorem canonical37718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37718 raw37718Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw37718 raw37718Labels = mixedMoment B raw37718step0 raw37718step0Labels := by
      have hz : ∀ j, raw37718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37718step0 = (fun i j => raw37718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37718step0 raw37718; decide +kernel
      have hl : raw37718step0Labels = raw37718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37718 raw37718Labels permutation346 hz
    mixedMoment B raw37718step0 raw37718step0Labels = mixedMoment B raw37718step1 raw37718step1Labels := by
      have ha : raw37718step1 = (fun i j => raw37718step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37718step1 raw37718step0; decide +kernel
      have hl : raw37718step1Labels = raw37718step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37718step0 raw37718step0Labels permutation33 permutation4
    mixedMoment B raw37718step1 raw37718step1Labels = mixedMoment B raw37718step2 raw37718step2Labels := by
      have ha : raw37718step2 = -raw37718step1 := by apply Matrix.ext; change ∀ i j, raw37718step2 i j = -(raw37718step1 i j); unfold raw37718step2 raw37718step1; decide +kernel
      have hl : raw37718step2Labels = raw37718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2153 node2153Labels := by rfl

theorem canonical37719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37719 raw37719Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw37719 raw37719Labels = mixedMoment B raw37719step0 raw37719step0Labels := by
      have hz : ∀ j, raw37719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37719step0 = (fun i j => raw37719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37719step0 raw37719; decide +kernel
      have hl : raw37719step0Labels = raw37719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37719 raw37719Labels permutation346 hz
    mixedMoment B raw37719step0 raw37719step0Labels = mixedMoment B raw37719step1 raw37719step1Labels := by
      have ha : raw37719step1 = (fun i j => raw37719step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37719step1 raw37719step0; decide +kernel
      have hl : raw37719step1Labels = raw37719step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37719step0 raw37719step0Labels permutation32 permutation4
    mixedMoment B raw37719step1 raw37719step1Labels = mixedMoment B raw37719step2 raw37719step2Labels := by
      have ha : raw37719step2 = -raw37719step1 := by apply Matrix.ext; change ∀ i j, raw37719step2 i j = -(raw37719step1 i j); unfold raw37719step2 raw37719step1; decide +kernel
      have hl : raw37719step2Labels = raw37719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical37720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37720 raw37720Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw37720 raw37720Labels = mixedMoment B raw37720step0 raw37720step0Labels := by
      have hz : ∀ j, raw37720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37720step0 = (fun i j => raw37720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37720step0 raw37720; decide +kernel
      have hl : raw37720step0Labels = raw37720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37720 raw37720Labels permutation346 hz
    mixedMoment B raw37720step0 raw37720step0Labels = mixedMoment B raw37720step1 raw37720step1Labels := by
      have ha : raw37720step1 = -raw37720step0 := by apply Matrix.ext; change ∀ i j, raw37720step1 i j = -(raw37720step0 i j); unfold raw37720step1 raw37720step0; decide +kernel
      have hl : raw37720step1Labels = raw37720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical37721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37721 raw37721Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw37721 raw37721Labels = mixedMoment B raw37721step0 raw37721step0Labels := by
      have hz : ∀ j, raw37721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37721step0 = (fun i j => raw37721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37721step0 raw37721; decide +kernel
      have hl : raw37721step0Labels = raw37721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37721 raw37721Labels permutation346 hz
    mixedMoment B raw37721step0 raw37721step0Labels = mixedMoment B raw37721step1 raw37721step1Labels := by
      have ha : raw37721step1 = (fun i j => raw37721step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37721step1 raw37721step0; decide +kernel
      have hl : raw37721step1Labels = raw37721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37721step0 raw37721step0Labels permutation144 permutation2
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical37722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37722 raw37722Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw37722 raw37722Labels = mixedMoment B raw37722step0 raw37722step0Labels := by
      have hz : ∀ j, raw37722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37722step0 = (fun i j => raw37722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37722step0 raw37722; decide +kernel
      have hl : raw37722step0Labels = raw37722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37722 raw37722Labels permutation346 hz
    mixedMoment B raw37722step0 raw37722step0Labels = mixedMoment B raw37722step1 raw37722step1Labels := by
      have ha : raw37722step1 = (fun i j => raw37722step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37722step1 raw37722step0; decide +kernel
      have hl : raw37722step1Labels = raw37722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37722step0 raw37722step0Labels permutation144 permutation2
    _ = mixedMoment B node2180 node2180Labels := by rfl

theorem canonical37723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37723 raw37723Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw37723 raw37723Labels = mixedMoment B raw37723step0 raw37723step0Labels := by
      have ha : raw37723step0 = (fun i j => raw37723 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37723step0 raw37723; decide +kernel
      have hl : raw37723step0Labels = raw37723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37723 raw37723Labels permutation170 permutation4
    mixedMoment B raw37723step0 raw37723step0Labels = mixedMoment B raw37723step1 raw37723step1Labels := by
      have ha : raw37723step1 = -raw37723step0 := by apply Matrix.ext; change ∀ i j, raw37723step1 i j = -(raw37723step0 i j); unfold raw37723step1 raw37723step0; decide +kernel
      have hl : raw37723step1Labels = raw37723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2160 node2160Labels := by rfl

theorem canonical37724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37724 raw37724Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw37724 raw37724Labels = mixedMoment B raw37724step0 raw37724step0Labels := by
      have hz : ∀ j, raw37724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37724step0 = (fun i j => raw37724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37724step0 raw37724; decide +kernel
      have hl : raw37724step0Labels = raw37724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37724 raw37724Labels permutation346 hz
    mixedMoment B raw37724step0 raw37724step0Labels = mixedMoment B raw37724step1 raw37724step1Labels := by
      have ha : raw37724step1 = (fun i j => raw37724step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37724step1 raw37724step0; decide +kernel
      have hl : raw37724step1Labels = raw37724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37724step0 raw37724step0Labels permutation37 permutation4
    mixedMoment B raw37724step1 raw37724step1Labels = mixedMoment B raw37724step2 raw37724step2Labels := by
      have ha : raw37724step2 = -raw37724step1 := by apply Matrix.ext; change ∀ i j, raw37724step2 i j = -(raw37724step1 i j); unfold raw37724step2 raw37724step1; decide +kernel
      have hl : raw37724step2Labels = raw37724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical37725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37725 raw37725Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw37725 raw37725Labels = mixedMoment B raw37725step0 raw37725step0Labels := by
      have hz : ∀ j, raw37725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37725step0 = (fun i j => raw37725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37725step0 raw37725; decide +kernel
      have hl : raw37725step0Labels = raw37725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37725 raw37725Labels permutation346 hz
    mixedMoment B raw37725step0 raw37725step0Labels = mixedMoment B raw37725step1 raw37725step1Labels := by
      have ha : raw37725step1 = (fun i j => raw37725step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37725step1 raw37725step0; decide +kernel
      have hl : raw37725step1Labels = raw37725step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37725step0 raw37725step0Labels permutation36 permutation4
    mixedMoment B raw37725step1 raw37725step1Labels = mixedMoment B raw37725step2 raw37725step2Labels := by
      have ha : raw37725step2 = -raw37725step1 := by apply Matrix.ext; change ∀ i j, raw37725step2 i j = -(raw37725step1 i j); unfold raw37725step2 raw37725step1; decide +kernel
      have hl : raw37725step2Labels = raw37725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical37726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37726 raw37726Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw37726 raw37726Labels = mixedMoment B raw37726step0 raw37726step0Labels := by
      have hz : ∀ j, raw37726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37726step0 = (fun i j => raw37726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37726step0 raw37726; decide +kernel
      have hl : raw37726step0Labels = raw37726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37726 raw37726Labels permutation346 hz
    mixedMoment B raw37726step0 raw37726step0Labels = mixedMoment B raw37726step1 raw37726step1Labels := by
      have ha : raw37726step1 = (fun i j => raw37726step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37726step1 raw37726step0; decide +kernel
      have hl : raw37726step1Labels = raw37726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37726step0 raw37726step0Labels permutation32 permutation4
    mixedMoment B raw37726step1 raw37726step1Labels = mixedMoment B raw37726step2 raw37726step2Labels := by
      have ha : raw37726step2 = -raw37726step1 := by apply Matrix.ext; change ∀ i j, raw37726step2 i j = -(raw37726step1 i j); unfold raw37726step2 raw37726step1; decide +kernel
      have hl : raw37726step2Labels = raw37726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3588 node3588Labels := by rfl

theorem canonical37727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37727 raw37727Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw37727 raw37727Labels = mixedMoment B raw37727step0 raw37727step0Labels := by
      have hz : ∀ j, raw37727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37727step0 = (fun i j => raw37727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37727step0 raw37727; decide +kernel
      have hl : raw37727step0Labels = raw37727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37727 raw37727Labels permutation346 hz
    mixedMoment B raw37727step0 raw37727step0Labels = mixedMoment B raw37727step1 raw37727step1Labels := by
      have ha : raw37727step1 = (fun i j => raw37727step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37727step1 raw37727step0; decide +kernel
      have hl : raw37727step1Labels = raw37727step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37727step0 raw37727step0Labels permutation40 permutation4
    mixedMoment B raw37727step1 raw37727step1Labels = mixedMoment B raw37727step2 raw37727step2Labels := by
      have ha : raw37727step2 = -raw37727step1 := by apply Matrix.ext; change ∀ i j, raw37727step2 i j = -(raw37727step1 i j); unfold raw37727step2 raw37727step1; decide +kernel
      have hl : raw37727step2Labels = raw37727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical37728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37728 raw37728Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw37728 raw37728Labels = mixedMoment B raw37728step0 raw37728step0Labels := by
      have ha : raw37728step0 = (fun i j => raw37728 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37728step0 raw37728; decide +kernel
      have hl : raw37728step0Labels = raw37728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37728 raw37728Labels permutation160 permutation4
    mixedMoment B raw37728step0 raw37728step0Labels = mixedMoment B raw37728step1 raw37728step1Labels := by
      have ha : raw37728step1 = -raw37728step0 := by apply Matrix.ext; change ∀ i j, raw37728step1 i j = -(raw37728step0 i j); unfold raw37728step1 raw37728step0; decide +kernel
      have hl : raw37728step1Labels = raw37728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical37729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37729 raw37729Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw37729 raw37729Labels = mixedMoment B raw37729step0 raw37729step0Labels := by
      have hz : ∀ j, raw37729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37729step0 = (fun i j => raw37729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37729step0 raw37729; decide +kernel
      have hl : raw37729step0Labels = raw37729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37729 raw37729Labels permutation346 hz
    mixedMoment B raw37729step0 raw37729step0Labels = mixedMoment B raw37729step1 raw37729step1Labels := by
      have ha : raw37729step1 = (fun i j => raw37729step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37729step1 raw37729step0; decide +kernel
      have hl : raw37729step1Labels = raw37729step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37729step0 raw37729step0Labels permutation34 permutation4
    mixedMoment B raw37729step1 raw37729step1Labels = mixedMoment B raw37729step2 raw37729step2Labels := by
      have ha : raw37729step2 = -raw37729step1 := by apply Matrix.ext; change ∀ i j, raw37729step2 i j = -(raw37729step1 i j); unfold raw37729step2 raw37729step1; decide +kernel
      have hl : raw37729step2Labels = raw37729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical37730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37730 raw37730Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw37730 raw37730Labels = mixedMoment B raw37730step0 raw37730step0Labels := by
      have hz : ∀ j, raw37730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37730step0 = (fun i j => raw37730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37730step0 raw37730; decide +kernel
      have hl : raw37730step0Labels = raw37730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37730 raw37730Labels permutation346 hz
    mixedMoment B raw37730step0 raw37730step0Labels = mixedMoment B raw37730step1 raw37730step1Labels := by
      have ha : raw37730step1 = (fun i j => raw37730step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37730step1 raw37730step0; decide +kernel
      have hl : raw37730step1Labels = raw37730step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37730step0 raw37730step0Labels permutation32 permutation4
    mixedMoment B raw37730step1 raw37730step1Labels = mixedMoment B raw37730step2 raw37730step2Labels := by
      have ha : raw37730step2 = -raw37730step1 := by apply Matrix.ext; change ∀ i j, raw37730step2 i j = -(raw37730step1 i j); unfold raw37730step2 raw37730step1; decide +kernel
      have hl : raw37730step2Labels = raw37730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical37731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37731 raw37731Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37731 raw37731Labels = mixedMoment B raw37731step0 raw37731step0Labels := by
      have hz : ∀ j, raw37731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37731step0 = (fun i j => raw37731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37731step0 raw37731; decide +kernel
      have hl : raw37731step0Labels = raw37731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37731 raw37731Labels permutation346 hz
    mixedMoment B raw37731step0 raw37731step0Labels = mixedMoment B raw37731step1 raw37731step1Labels := by
      have ha : raw37731step1 = (fun i j => raw37731step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37731step1 raw37731step0; decide +kernel
      have hl : raw37731step1Labels = raw37731step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37731step0 raw37731step0Labels permutation34 permutation2
    mixedMoment B raw37731step1 raw37731step1Labels = mixedMoment B raw37731step2 raw37731step2Labels := by
      have ha : raw37731step2 = -raw37731step1 := by apply Matrix.ext; change ∀ i j, raw37731step2 i j = -(raw37731step1 i j); unfold raw37731step2 raw37731step1; decide +kernel
      have hl : raw37731step2Labels = raw37731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical37732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37732 raw37732Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw37732 raw37732Labels = mixedMoment B raw37732step0 raw37732step0Labels := by
      have ha : raw37732step0 = (fun i j => raw37732 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37732step0 raw37732; decide +kernel
      have hl : raw37732step0Labels = raw37732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37732 raw37732Labels permutation158 permutation4
    mixedMoment B raw37732step0 raw37732step0Labels = mixedMoment B raw37732step1 raw37732step1Labels := by
      have ha : raw37732step1 = -raw37732step0 := by apply Matrix.ext; change ∀ i j, raw37732step1 i j = -(raw37732step0 i j); unfold raw37732step1 raw37732step0; decide +kernel
      have hl : raw37732step1Labels = raw37732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical37733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37733 raw37733Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw37733 raw37733Labels = mixedMoment B raw37733step0 raw37733step0Labels := by
      have hz : ∀ j, raw37733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37733step0 = (fun i j => raw37733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37733step0 raw37733; decide +kernel
      have hl : raw37733step0Labels = raw37733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37733 raw37733Labels permutation346 hz
    mixedMoment B raw37733step0 raw37733step0Labels = mixedMoment B raw37733step1 raw37733step1Labels := by
      have ha : raw37733step1 = (fun i j => raw37733step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37733step1 raw37733step0; decide +kernel
      have hl : raw37733step1Labels = raw37733step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37733step0 raw37733step0Labels permutation32 permutation4
    mixedMoment B raw37733step1 raw37733step1Labels = mixedMoment B raw37733step2 raw37733step2Labels := by
      have ha : raw37733step2 = -raw37733step1 := by apply Matrix.ext; change ∀ i j, raw37733step2 i j = -(raw37733step1 i j); unfold raw37733step2 raw37733step1; decide +kernel
      have hl : raw37733step2Labels = raw37733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3420 node3420Labels := by rfl

theorem canonical37734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37734 raw37734Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw37734 raw37734Labels = mixedMoment B raw37734step0 raw37734step0Labels := by
      have hz : ∀ j, raw37734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37734step0 = (fun i j => raw37734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37734step0 raw37734; decide +kernel
      have hl : raw37734step0Labels = raw37734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37734 raw37734Labels permutation346 hz
    mixedMoment B raw37734step0 raw37734step0Labels = mixedMoment B raw37734step1 raw37734step1Labels := by
      have ha : raw37734step1 = (fun i j => raw37734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37734step1 raw37734step0; decide +kernel
      have hl : raw37734step1Labels = raw37734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37734step0 raw37734step0Labels permutation33 permutation4
    mixedMoment B raw37734step1 raw37734step1Labels = mixedMoment B raw37734step2 raw37734step2Labels := by
      have ha : raw37734step2 = -raw37734step1 := by apply Matrix.ext; change ∀ i j, raw37734step2 i j = -(raw37734step1 i j); unfold raw37734step2 raw37734step1; decide +kernel
      have hl : raw37734step2Labels = raw37734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical37735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37735 raw37735Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37735 raw37735Labels = mixedMoment B raw37735step0 raw37735step0Labels := by
      have hz : ∀ j, raw37735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37735step0 = (fun i j => raw37735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37735step0 raw37735; decide +kernel
      have hl : raw37735step0Labels = raw37735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37735 raw37735Labels permutation346 hz
    mixedMoment B raw37735step0 raw37735step0Labels = mixedMoment B raw37735step1 raw37735step1Labels := by
      have ha : raw37735step1 = (fun i j => raw37735step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37735step1 raw37735step0; decide +kernel
      have hl : raw37735step1Labels = raw37735step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37735step0 raw37735step0Labels permutation32 permutation4
    mixedMoment B raw37735step1 raw37735step1Labels = mixedMoment B raw37735step2 raw37735step2Labels := by
      have ha : raw37735step2 = -raw37735step1 := by apply Matrix.ext; change ∀ i j, raw37735step2 i j = -(raw37735step1 i j); unfold raw37735step2 raw37735step1; decide +kernel
      have hl : raw37735step2Labels = raw37735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical37736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37736 raw37736Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw37736 raw37736Labels = mixedMoment B raw37736step0 raw37736step0Labels := by
      have hz : ∀ j, raw37736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37736step0 = (fun i j => raw37736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37736step0 raw37736; decide +kernel
      have hl : raw37736step0Labels = raw37736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37736 raw37736Labels permutation346 hz
    mixedMoment B raw37736step0 raw37736step0Labels = mixedMoment B raw37736step1 raw37736step1Labels := by
      have ha : raw37736step1 = (fun i j => raw37736step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37736step1 raw37736step0; decide +kernel
      have hl : raw37736step1Labels = raw37736step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37736step0 raw37736step0Labels permutation145 permutation2
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical37737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37737 raw37737Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw37737 raw37737Labels = mixedMoment B raw37737step0 raw37737step0Labels := by
      have ha : raw37737step0 = (fun i j => raw37737 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37737step0 raw37737; decide +kernel
      have hl : raw37737step0Labels = raw37737Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37737 raw37737Labels permutation664 permutation2
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical37738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37738 raw37738Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw37738 raw37738Labels = mixedMoment B raw37738step0 raw37738step0Labels := by
      have hz : ∀ j, raw37738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37738step0 = (fun i j => raw37738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37738step0 raw37738; decide +kernel
      have hl : raw37738step0Labels = raw37738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37738 raw37738Labels permutation346 hz
    mixedMoment B raw37738step0 raw37738step0Labels = mixedMoment B raw37738step1 raw37738step1Labels := by
      have ha : raw37738step1 = (fun i j => raw37738step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37738step1 raw37738step0; decide +kernel
      have hl : raw37738step1Labels = raw37738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37738step0 raw37738step0Labels permutation151 permutation2
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical37739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37739 raw37739Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw37739 raw37739Labels = mixedMoment B raw37739step0 raw37739step0Labels := by
      have hz : ∀ j, raw37739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37739step0 = (fun i j => raw37739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37739step0 raw37739; decide +kernel
      have hl : raw37739step0Labels = raw37739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37739 raw37739Labels permutation346 hz
    mixedMoment B raw37739step0 raw37739step0Labels = mixedMoment B raw37739step1 raw37739step1Labels := by
      have ha : raw37739step1 = (fun i j => raw37739step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37739step1 raw37739step0; decide +kernel
      have hl : raw37739step1Labels = raw37739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37739step0 raw37739step0Labels permutation145 permutation2
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical37740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37740 raw37740Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw37740 raw37740Labels = mixedMoment B raw37740step0 raw37740step0Labels := by
      have hz : ∀ j, raw37740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37740step0 = (fun i j => raw37740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37740step0 raw37740; decide +kernel
      have hl : raw37740step0Labels = raw37740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37740 raw37740Labels permutation346 hz
    mixedMoment B raw37740step0 raw37740step0Labels = mixedMoment B raw37740step1 raw37740step1Labels := by
      have ha : raw37740step1 = -raw37740step0 := by apply Matrix.ext; change ∀ i j, raw37740step1 i j = -(raw37740step0 i j); unfold raw37740step1 raw37740step0; decide +kernel
      have hl : raw37740step1Labels = raw37740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3420 node3420Labels := by rfl

theorem canonical37741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37741 raw37741Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw37741 raw37741Labels = mixedMoment B raw37741step0 raw37741step0Labels := by
      have ha : raw37741step0 = (fun i j => raw37741 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37741step0 raw37741; decide +kernel
      have hl : raw37741step0Labels = raw37741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37741 raw37741Labels permutation160 permutation4
    mixedMoment B raw37741step0 raw37741step0Labels = mixedMoment B raw37741step1 raw37741step1Labels := by
      have ha : raw37741step1 = -raw37741step0 := by apply Matrix.ext; change ∀ i j, raw37741step1 i j = -(raw37741step0 i j); unfold raw37741step1 raw37741step0; decide +kernel
      have hl : raw37741step1Labels = raw37741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3403 node3403Labels := by rfl

theorem canonical37742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37742 raw37742Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37742 raw37742Labels = mixedMoment B raw37742step0 raw37742step0Labels := by
      have hz : ∀ j, raw37742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37742step0 = (fun i j => raw37742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37742step0 raw37742; decide +kernel
      have hl : raw37742step0Labels = raw37742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37742 raw37742Labels permutation346 hz
    mixedMoment B raw37742step0 raw37742step0Labels = mixedMoment B raw37742step1 raw37742step1Labels := by
      have ha : raw37742step1 = (fun i j => raw37742step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37742step1 raw37742step0; decide +kernel
      have hl : raw37742step1Labels = raw37742step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37742step0 raw37742step0Labels permutation34 permutation4
    mixedMoment B raw37742step1 raw37742step1Labels = mixedMoment B raw37742step2 raw37742step2Labels := by
      have ha : raw37742step2 = -raw37742step1 := by apply Matrix.ext; change ∀ i j, raw37742step2 i j = -(raw37742step1 i j); unfold raw37742step2 raw37742step1; decide +kernel
      have hl : raw37742step2Labels = raw37742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

theorem canonical37743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37743 raw37743Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw37743 raw37743Labels = mixedMoment B raw37743step0 raw37743step0Labels := by
      have hz : ∀ j, raw37743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37743step0 = (fun i j => raw37743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37743step0 raw37743; decide +kernel
      have hl : raw37743step0Labels = raw37743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37743 raw37743Labels permutation346 hz
    mixedMoment B raw37743step0 raw37743step0Labels = mixedMoment B raw37743step1 raw37743step1Labels := by
      have ha : raw37743step1 = (fun i j => raw37743step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37743step1 raw37743step0; decide +kernel
      have hl : raw37743step1Labels = raw37743step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37743step0 raw37743step0Labels permutation145 permutation4
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical37747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37747 raw37747Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw37747 raw37747Labels = mixedMoment B raw37747step0 raw37747step0Labels := by
      have ha : raw37747step0 = (fun i j => raw37747 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37747step0 raw37747; decide +kernel
      have hl : raw37747step0Labels = raw37747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37747 raw37747Labels permutation662 permutation4
    _ = mixedMoment B node2176 node2176Labels := by rfl

theorem canonical37748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37748 raw37748Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw37748 raw37748Labels = mixedMoment B raw37748step0 raw37748step0Labels := by
      have hz : ∀ j, raw37748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37748step0 = (fun i j => raw37748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37748step0 raw37748; decide +kernel
      have hl : raw37748step0Labels = raw37748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37748 raw37748Labels permutation346 hz
    mixedMoment B raw37748step0 raw37748step0Labels = mixedMoment B raw37748step1 raw37748step1Labels := by
      have ha : raw37748step1 = (fun i j => raw37748step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37748step1 raw37748step0; decide +kernel
      have hl : raw37748step1Labels = raw37748step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37748step0 raw37748step0Labels permutation149 permutation4
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical37749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37749 raw37749Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw37749 raw37749Labels = mixedMoment B raw37749step0 raw37749step0Labels := by
      have hz : ∀ j, raw37749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37749step0 = (fun i j => raw37749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37749step0 raw37749; decide +kernel
      have hl : raw37749step0Labels = raw37749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37749 raw37749Labels permutation346 hz
    mixedMoment B raw37749step0 raw37749step0Labels = mixedMoment B raw37749step1 raw37749step1Labels := by
      have ha : raw37749step1 = (fun i j => raw37749step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37749step1 raw37749step0; decide +kernel
      have hl : raw37749step1Labels = raw37749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37749step0 raw37749step0Labels permutation143 permutation4
    _ = mixedMoment B node2212 node2212Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2140 node2140Labels = Sparse.eval nodeValue2140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2140) = mixedMoment B node2140 node2140Labels := rfl
  simpa [nodeValue2140, Sparse.eval] using hc.symm

theorem sound2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2143 node2143Labels = Sparse.eval nodeValue2143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2143) = mixedMoment B node2143 node2143Labels := rfl
  simpa [nodeValue2143, Sparse.eval] using hc.symm

theorem sound2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2147 node2147Labels = Sparse.eval nodeValue2147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2147) = mixedMoment B node2147 node2147Labels := rfl
  simpa [nodeValue2147, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2153 node2153Labels = Sparse.eval nodeValue2153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2153) = mixedMoment B node2153 node2153Labels := rfl
  simpa [nodeValue2153, Sparse.eval] using hc.symm

theorem sound2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2155 node2155Labels = Sparse.eval nodeValue2155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2155) = mixedMoment B node2155 node2155Labels := rfl
  simpa [nodeValue2155, Sparse.eval] using hc.symm

theorem sound2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2159 node2159Labels = Sparse.eval nodeValue2159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2159) = mixedMoment B node2159 node2159Labels := rfl
  simpa [nodeValue2159, Sparse.eval] using hc.symm

theorem sound2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2160 node2160Labels = Sparse.eval nodeValue2160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2160) = mixedMoment B node2160 node2160Labels := rfl
  simpa [nodeValue2160, Sparse.eval] using hc.symm

theorem sound2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2161 node2161Labels = Sparse.eval nodeValue2161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2161) = mixedMoment B node2161 node2161Labels := rfl
  simpa [nodeValue2161, Sparse.eval] using hc.symm

theorem sound2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2162 node2162Labels = Sparse.eval nodeValue2162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2162) = mixedMoment B node2162 node2162Labels := rfl
  simpa [nodeValue2162, Sparse.eval] using hc.symm

theorem sound2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2163 node2163Labels = Sparse.eval nodeValue2163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2163) = mixedMoment B node2163 node2163Labels := rfl
  simpa [nodeValue2163, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2176 node2176Labels = Sparse.eval nodeValue2176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2176) = mixedMoment B node2176 node2176Labels := rfl
  simpa [nodeValue2176, Sparse.eval] using hc.symm

theorem sound2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2180 node2180Labels = Sparse.eval nodeValue2180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2180) = mixedMoment B node2180 node2180Labels := rfl
  simpa [nodeValue2180, Sparse.eval] using hc.symm

theorem sound2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2181 node2181Labels = Sparse.eval nodeValue2181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2181) = mixedMoment B node2181 node2181Labels := rfl
  simpa [nodeValue2181, Sparse.eval] using hc.symm

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2239 node2239Labels = Sparse.eval nodeValue2239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2239) = mixedMoment B node2239 node2239Labels := rfl
  simpa [nodeValue2239, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2273 node2273Labels = Sparse.eval nodeValue2273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2273) = mixedMoment B node2273 node2273Labels := rfl
  simpa [nodeValue2273, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3264 node3264Labels = Sparse.eval nodeValue3264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3264) = mixedMoment B node3264 node3264Labels := rfl
  simpa [nodeValue3264, Sparse.eval] using hc.symm

theorem sound3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3265 node3265Labels = Sparse.eval nodeValue3265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3265) = mixedMoment B node3265 node3265Labels := rfl
  simpa [nodeValue3265, Sparse.eval] using hc.symm

theorem sound3270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3270 node3270Labels = Sparse.eval nodeValue3270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3270) = mixedMoment B node3270 node3270Labels := rfl
  simpa [nodeValue3270, Sparse.eval] using hc.symm

theorem sound3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3273 node3273Labels = Sparse.eval nodeValue3273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3273) = mixedMoment B node3273 node3273Labels := rfl
  simpa [nodeValue3273, Sparse.eval] using hc.symm

theorem sound3274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3274 node3274Labels = Sparse.eval nodeValue3274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3274) = mixedMoment B node3274 node3274Labels := rfl
  simpa [nodeValue3274, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = 0 := by
  exact mixedMoment_alpha B hF node3403 node3403Labels 1 permutation485
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = Sparse.eval nodeValue3403 (mixedVector B) := by
  simpa only [nodeValue3403, Sparse.eval_nil] using zero3403 B _hB _hF

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3419 node3419Labels = Sparse.eval nodeValue3419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3419) = mixedMoment B node3419 node3419Labels := rfl
  simpa [nodeValue3419, Sparse.eval] using hc.symm

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

theorem sound3422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3422 node3422Labels = Sparse.eval nodeValue3422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3422) = mixedMoment B node3422 node3422Labels := rfl
  simpa [nodeValue3422, Sparse.eval] using hc.symm

theorem sound3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3423 node3423Labels = Sparse.eval nodeValue3423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3423) = mixedMoment B node3423 node3423Labels := rfl
  simpa [nodeValue3423, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3512 node3512Labels = Sparse.eval nodeValue3512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3512) = mixedMoment B node3512 node3512Labels := rfl
  simpa [nodeValue3512, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3596 node3596Labels = Sparse.eval nodeValue3596 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3596) = mixedMoment B node3596 node3596Labels := rfl
  simpa [nodeValue3596, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4064 node4064Labels = Sparse.eval nodeValue4064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4064) = mixedMoment B node4064 node4064Labels := rfl
  simpa [nodeValue4064, Sparse.eval] using hc.symm

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

theorem sound4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4074 node4074Labels = Sparse.eval nodeValue4074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4074) = mixedMoment B node4074 node4074Labels := rfl
  simpa [nodeValue4074, Sparse.eval] using hc.symm

theorem sound4076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4076 node4076Labels = Sparse.eval nodeValue4076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4076) = mixedMoment B node4076 node4076Labels := rfl
  simpa [nodeValue4076, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources85
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2720 + difference 0 2) (sourceB2720 + difference 2 0) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA2720 + difference 0 2) (sourceB2720 + difference 2 0) sourceC2720) = raw37622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37622; decide +kernel
    rw [ha]
    exact (canonical37622 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2720 + difference 1 2) (sourceB2720 + difference 2 1) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA2720 + difference 1 2) (sourceB2720 + difference 2 1) sourceC2720) = raw37623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37623; decide +kernel
    rw [ha]
    exact (canonical37623 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2720 + difference 2 2) (sourceB2720 + difference 2 2) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2720 + difference 2 2) (sourceB2720 + difference 2 2) sourceC2720) = raw37624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37624; decide +kernel
    rw [ha]
    exact (canonical37624 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2720 + difference 3 2) (sourceB2720 + difference 2 3) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2720 + difference 3 2) (sourceB2720 + difference 2 3) sourceC2720) = raw37625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37625; decide +kernel
    rw [ha]
    exact (canonical37625 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2720 + difference 4 2) (sourceB2720 + difference 2 4) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2720 + difference 4 2) (sourceB2720 + difference 2 4) sourceC2720) = raw37626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37626; decide +kernel
    rw [ha]
    exact (canonical37626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2720 + difference 5 2) (sourceB2720 + difference 2 5) sourceC2720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2720 + difference 5 2) (sourceB2720 + difference 2 5) sourceC2720) = raw37627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2720 sourceB2720 sourceC2720 difference raw37627; decide +kernel
    rw [ha]
    exact (canonical37627 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2720 + sourceB2720) sourceC2720) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2720 + sourceB2720) sourceC2720) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2720 sourceB2720 sourceC2720 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2720 sourceB2720 sourceC2720
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2720, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2725 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2725 + difference 0 5) (sourceB2725 + difference 5 0) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2725 + difference 0 5) (sourceB2725 + difference 5 0) sourceC2725) = raw37648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37648; decide +kernel
    rw [ha]
    exact (canonical37648 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2725 + difference 1 5) (sourceB2725 + difference 5 1) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2725 + difference 1 5) (sourceB2725 + difference 5 1) sourceC2725) = raw37649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37649; decide +kernel
    rw [ha]
    exact (canonical37649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2725 + difference 2 5) (sourceB2725 + difference 5 2) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2725 + difference 2 5) (sourceB2725 + difference 5 2) sourceC2725) = raw37650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37650; decide +kernel
    rw [ha]
    exact (canonical37650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2725 + difference 3 5) (sourceB2725 + difference 5 3) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2725 + difference 3 5) (sourceB2725 + difference 5 3) sourceC2725) = raw37651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37651; decide +kernel
    rw [ha]
    exact (canonical37651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2725 + difference 4 5) (sourceB2725 + difference 5 4) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2725 + difference 4 5) (sourceB2725 + difference 5 4) sourceC2725) = raw37652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37652; decide +kernel
    rw [ha]
    exact (canonical37652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2725 + difference 5 5) (sourceB2725 + difference 5 5) sourceC2725) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2725 + difference 5 5) (sourceB2725 + difference 5 5) sourceC2725) = raw37653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2725 sourceB2725 sourceC2725 difference raw37653; decide +kernel
    rw [ha]
    exact (canonical37653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2725 + sourceB2725) sourceC2725) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2725 + sourceB2725) sourceC2725) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2725 sourceB2725 sourceC2725 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2725 sourceB2725 sourceC2725
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2725, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2726 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2726 + difference 0 2) (sourceB2726 + difference 2 0) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA2726 + difference 0 2) (sourceB2726 + difference 2 0) sourceC2726) = raw37654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37654; decide +kernel
    rw [ha]
    exact (canonical37654 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2726 + difference 1 2) (sourceB2726 + difference 2 1) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2726 + difference 1 2) (sourceB2726 + difference 2 1) sourceC2726) = raw37655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37655; decide +kernel
    rw [ha]
    exact (canonical37655 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2726 + difference 2 2) (sourceB2726 + difference 2 2) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2726 + difference 2 2) (sourceB2726 + difference 2 2) sourceC2726) = raw37656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37656; decide +kernel
    rw [ha]
    exact (canonical37656 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2726 + difference 3 2) (sourceB2726 + difference 2 3) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2726 + difference 3 2) (sourceB2726 + difference 2 3) sourceC2726) = raw37657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37657; decide +kernel
    rw [ha]
    exact (canonical37657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2726 + difference 4 2) (sourceB2726 + difference 2 4) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2726 + difference 4 2) (sourceB2726 + difference 2 4) sourceC2726) = raw37658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37658; decide +kernel
    rw [ha]
    exact (canonical37658 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2726 + difference 5 2) (sourceB2726 + difference 2 5) sourceC2726) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2726 + difference 5 2) (sourceB2726 + difference 2 5) sourceC2726) = raw37652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2726 sourceB2726 sourceC2726 difference raw37652; decide +kernel
    rw [ha]
    exact (canonical37652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2726 + sourceB2726) sourceC2726) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (doubleCharges (sourceA2726 + sourceB2726) sourceC2726) = raw37647 := by
      apply Matrix.ext; unfold doubleCharges sourceA2726 sourceB2726 sourceC2726 raw37647; decide +kernel
    rw [ha]
    exact (canonical37647 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2726 sourceB2726 sourceC2726
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2726, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2728 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2728 + difference 0 4) (sourceB2728 + difference 4 0) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2728 + difference 0 4) (sourceB2728 + difference 4 0) sourceC2728) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2728 + difference 1 4) (sourceB2728 + difference 4 1) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2728 + difference 1 4) (sourceB2728 + difference 4 1) sourceC2728) = raw37666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37666; decide +kernel
    rw [ha]
    exact (canonical37666 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2728 + difference 2 4) (sourceB2728 + difference 4 2) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2728 + difference 2 4) (sourceB2728 + difference 4 2) sourceC2728) = raw37667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37667; decide +kernel
    rw [ha]
    exact (canonical37667 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2728 + difference 3 4) (sourceB2728 + difference 4 3) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2728 + difference 3 4) (sourceB2728 + difference 4 3) sourceC2728) = raw37668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37668; decide +kernel
    rw [ha]
    exact (canonical37668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2728 + difference 4 4) (sourceB2728 + difference 4 4) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2728 + difference 4 4) (sourceB2728 + difference 4 4) sourceC2728) = raw37669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37669; decide +kernel
    rw [ha]
    exact (canonical37669 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2728 + difference 5 4) (sourceB2728 + difference 4 5) sourceC2728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2728 + difference 5 4) (sourceB2728 + difference 4 5) sourceC2728) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2728 sourceB2728 sourceC2728 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2728 + sourceB2728) sourceC2728) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2728 + sourceB2728) sourceC2728) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2728 sourceB2728 sourceC2728 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2728 sourceB2728 sourceC2728
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2728, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2729 + difference 0 3) (sourceB2729 + difference 3 0) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2729 + difference 0 3) (sourceB2729 + difference 3 0) sourceC2729) = raw37672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37672; decide +kernel
    rw [ha]
    exact (canonical37672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2729 + difference 1 3) (sourceB2729 + difference 3 1) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2729 + difference 1 3) (sourceB2729 + difference 3 1) sourceC2729) = raw37673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37673; decide +kernel
    rw [ha]
    exact (canonical37673 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2729 + difference 2 3) (sourceB2729 + difference 3 2) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2729 + difference 2 3) (sourceB2729 + difference 3 2) sourceC2729) = raw37674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37674; decide +kernel
    rw [ha]
    exact (canonical37674 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2729 + difference 3 3) (sourceB2729 + difference 3 3) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2729 + difference 3 3) (sourceB2729 + difference 3 3) sourceC2729) = raw37675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37675; decide +kernel
    rw [ha]
    exact (canonical37675 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2729 + difference 4 3) (sourceB2729 + difference 3 4) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2729 + difference 4 3) (sourceB2729 + difference 3 4) sourceC2729) = raw37676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37676; decide +kernel
    rw [ha]
    exact (canonical37676 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2729 + difference 5 3) (sourceB2729 + difference 3 5) sourceC2729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2729 + difference 5 3) (sourceB2729 + difference 3 5) sourceC2729) = raw37677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2729 sourceB2729 sourceC2729 difference raw37677; decide +kernel
    rw [ha]
    exact (canonical37677 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2729 + sourceB2729) sourceC2729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2729 + sourceB2729) sourceC2729) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2729 sourceB2729 sourceC2729 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2729 sourceB2729 sourceC2729
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2729, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2730 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2730 + difference 0 3) (sourceB2730 + difference 3 0) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2730 + difference 0 3) (sourceB2730 + difference 3 0) sourceC2730) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2730 + difference 1 3) (sourceB2730 + difference 3 1) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2730 + difference 1 3) (sourceB2730 + difference 3 1) sourceC2730) = raw37679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37679; decide +kernel
    rw [ha]
    exact (canonical37679 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2730 + difference 2 3) (sourceB2730 + difference 3 2) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2730 + difference 2 3) (sourceB2730 + difference 3 2) sourceC2730) = raw37680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37680; decide +kernel
    rw [ha]
    exact (canonical37680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2730 + difference 3 3) (sourceB2730 + difference 3 3) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2730 + difference 3 3) (sourceB2730 + difference 3 3) sourceC2730) = raw37681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37681; decide +kernel
    rw [ha]
    exact (canonical37681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2730 + difference 4 3) (sourceB2730 + difference 3 4) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2730 + difference 4 3) (sourceB2730 + difference 3 4) sourceC2730) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2730 + difference 5 3) (sourceB2730 + difference 3 5) sourceC2730) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2730 + difference 5 3) (sourceB2730 + difference 3 5) sourceC2730) = raw37676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2730 sourceB2730 sourceC2730 difference raw37676; decide +kernel
    rw [ha]
    exact (canonical37676 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2730 + sourceB2730) sourceC2730) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2730 + sourceB2730) sourceC2730) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2730 sourceB2730 sourceC2730 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2730 sourceB2730 sourceC2730
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2730, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2731 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2731 + difference 0 3) (sourceB2731 + difference 3 0) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2731 + difference 0 3) (sourceB2731 + difference 3 0) sourceC2731) = raw37682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37682; decide +kernel
    rw [ha]
    exact (canonical37682 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2731 + difference 1 3) (sourceB2731 + difference 3 1) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2731 + difference 1 3) (sourceB2731 + difference 3 1) sourceC2731) = raw37672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37672; decide +kernel
    rw [ha]
    exact (canonical37672 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2731 + difference 2 3) (sourceB2731 + difference 3 2) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2731 + difference 2 3) (sourceB2731 + difference 3 2) sourceC2731) = raw37683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37683; decide +kernel
    rw [ha]
    exact (canonical37683 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2731 + difference 3 3) (sourceB2731 + difference 3 3) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2731 + difference 3 3) (sourceB2731 + difference 3 3) sourceC2731) = raw37684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37684; decide +kernel
    rw [ha]
    exact (canonical37684 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2731 + difference 4 3) (sourceB2731 + difference 3 4) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2731 + difference 4 3) (sourceB2731 + difference 3 4) sourceC2731) = raw37685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37685; decide +kernel
    rw [ha]
    exact (canonical37685 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2731 + difference 5 3) (sourceB2731 + difference 3 5) sourceC2731) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2731 + difference 5 3) (sourceB2731 + difference 3 5) sourceC2731) = raw37686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2731 sourceB2731 sourceC2731 difference raw37686; decide +kernel
    rw [ha]
    exact (canonical37686 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2731 + sourceB2731) sourceC2731) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2731 + sourceB2731) sourceC2731) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2731 sourceB2731 sourceC2731 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2731 sourceB2731 sourceC2731
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2731, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2732 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2732 + difference 0 3) (sourceB2732 + difference 3 0) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2732 + difference 0 3) (sourceB2732 + difference 3 0) sourceC2732) = raw37687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37687; decide +kernel
    rw [ha]
    exact (canonical37687 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2732 + difference 1 3) (sourceB2732 + difference 3 1) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2732 + difference 1 3) (sourceB2732 + difference 3 1) sourceC2732) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2732 + difference 2 3) (sourceB2732 + difference 3 2) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2732 + difference 2 3) (sourceB2732 + difference 3 2) sourceC2732) = raw37688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37688; decide +kernel
    rw [ha]
    exact (canonical37688 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2732 + difference 3 3) (sourceB2732 + difference 3 3) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2732 + difference 3 3) (sourceB2732 + difference 3 3) sourceC2732) = raw37689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37689; decide +kernel
    rw [ha]
    exact (canonical37689 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2732 + difference 4 3) (sourceB2732 + difference 3 4) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2732 + difference 4 3) (sourceB2732 + difference 3 4) sourceC2732) = raw37690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37690; decide +kernel
    rw [ha]
    exact (canonical37690 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2732 + difference 5 3) (sourceB2732 + difference 3 5) sourceC2732) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2732 + difference 5 3) (sourceB2732 + difference 3 5) sourceC2732) = raw37685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2732 sourceB2732 sourceC2732 difference raw37685; decide +kernel
    rw [ha]
    exact (canonical37685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2732 + sourceB2732) sourceC2732) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2732 + sourceB2732) sourceC2732) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2732 sourceB2732 sourceC2732 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2732 sourceB2732 sourceC2732
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2732, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2733 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 0) (sourceB2733 + difference 0 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 0) (sourceB2733 + difference 0 2) sourceC2733) = raw37670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37670; decide +kernel
    rw [ha]
    exact (canonical37670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 1) (sourceB2733 + difference 1 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 1) (sourceB2733 + difference 1 2) sourceC2733) = raw37690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37690; decide +kernel
    rw [ha]
    exact (canonical37690 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 2) (sourceB2733 + difference 2 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 2) (sourceB2733 + difference 2 2) sourceC2733) = raw37691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37691; decide +kernel
    rw [ha]
    exact (canonical37691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 3) (sourceB2733 + difference 3 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 3) (sourceB2733 + difference 3 2) sourceC2733) = raw37692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37692; decide +kernel
    rw [ha]
    exact (canonical37692 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 4) (sourceB2733 + difference 4 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 4) (sourceB2733 + difference 4 2) sourceC2733) = raw37678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37678; decide +kernel
    rw [ha]
    exact (canonical37678 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2733 + difference 2 5) (sourceB2733 + difference 5 2) sourceC2733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2733 + difference 2 5) (sourceB2733 + difference 5 2) sourceC2733) = raw37665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2733 sourceB2733 sourceC2733 difference raw37665; decide +kernel
    rw [ha]
    exact (canonical37665 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2733 + sourceB2733) sourceC2733) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (doubleCharges (sourceA2733 + sourceB2733) sourceC2733) = raw37671 := by
      apply Matrix.ext; unfold doubleCharges sourceA2733 sourceB2733 sourceC2733 raw37671; decide +kernel
    rw [ha]
    exact (canonical37671 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2733 sourceB2733 sourceC2733
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2733, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2740 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2740 + difference 0 4) (sourceB2740 + difference 4 0) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2740 + difference 0 4) (sourceB2740 + difference 4 0) sourceC2740) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2740 + difference 1 4) (sourceB2740 + difference 4 1) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2740 + difference 1 4) (sourceB2740 + difference 4 1) sourceC2740) = raw37715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37715; decide +kernel
    rw [ha]
    exact (canonical37715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2740 + difference 2 4) (sourceB2740 + difference 4 2) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2740 + difference 2 4) (sourceB2740 + difference 4 2) sourceC2740) = raw37716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37716; decide +kernel
    rw [ha]
    exact (canonical37716 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2740 + difference 3 4) (sourceB2740 + difference 4 3) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2740 + difference 3 4) (sourceB2740 + difference 4 3) sourceC2740) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2740 + difference 4 4) (sourceB2740 + difference 4 4) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2740 + difference 4 4) (sourceB2740 + difference 4 4) sourceC2740) = raw37718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37718; decide +kernel
    rw [ha]
    exact (canonical37718 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2740 + difference 5 4) (sourceB2740 + difference 4 5) sourceC2740) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2740 + difference 5 4) (sourceB2740 + difference 4 5) sourceC2740) = raw37719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2740 sourceB2740 sourceC2740 difference raw37719; decide +kernel
    rw [ha]
    exact (canonical37719 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2740 + sourceB2740) sourceC2740) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2740 + sourceB2740) sourceC2740) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2740 sourceB2740 sourceC2740 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2740 sourceB2740 sourceC2740
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2740, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2741 + difference 0 4) (sourceB2741 + difference 4 0) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2741 + difference 0 4) (sourceB2741 + difference 4 0) sourceC2741) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2741 + difference 1 4) (sourceB2741 + difference 4 1) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2741 + difference 1 4) (sourceB2741 + difference 4 1) sourceC2741) = raw37722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37722; decide +kernel
    rw [ha]
    exact (canonical37722 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2741 + difference 2 4) (sourceB2741 + difference 4 2) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2741 + difference 2 4) (sourceB2741 + difference 4 2) sourceC2741) = raw37723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37723; decide +kernel
    rw [ha]
    exact (canonical37723 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2741 + difference 3 4) (sourceB2741 + difference 4 3) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2741 + difference 3 4) (sourceB2741 + difference 4 3) sourceC2741) = raw37724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37724; decide +kernel
    rw [ha]
    exact (canonical37724 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2741 + difference 4 4) (sourceB2741 + difference 4 4) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2741 + difference 4 4) (sourceB2741 + difference 4 4) sourceC2741) = raw37725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37725; decide +kernel
    rw [ha]
    exact (canonical37725 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2741 + difference 5 4) (sourceB2741 + difference 4 5) sourceC2741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2741 + difference 5 4) (sourceB2741 + difference 4 5) sourceC2741) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2741 sourceB2741 sourceC2741 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2741 + sourceB2741) sourceC2741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2741 + sourceB2741) sourceC2741) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2741 sourceB2741 sourceC2741 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2741 sourceB2741 sourceC2741
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2741, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2742 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2742 + difference 0 2) (sourceB2742 + difference 2 0) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2742 + difference 0 2) (sourceB2742 + difference 2 0) sourceC2742) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2742 + difference 1 2) (sourceB2742 + difference 2 1) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2742 + difference 1 2) (sourceB2742 + difference 2 1) sourceC2742) = raw37727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37727; decide +kernel
    rw [ha]
    exact (canonical37727 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2742 + difference 2 2) (sourceB2742 + difference 2 2) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2742 + difference 2 2) (sourceB2742 + difference 2 2) sourceC2742) = raw37728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37728; decide +kernel
    rw [ha]
    exact (canonical37728 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2742 + difference 3 2) (sourceB2742 + difference 2 3) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2742 + difference 3 2) (sourceB2742 + difference 2 3) sourceC2742) = raw37729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37729; decide +kernel
    rw [ha]
    exact (canonical37729 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2742 + difference 4 2) (sourceB2742 + difference 2 4) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2742 + difference 4 2) (sourceB2742 + difference 2 4) sourceC2742) = raw37719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37719; decide +kernel
    rw [ha]
    exact (canonical37719 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2742 + difference 5 2) (sourceB2742 + difference 2 5) sourceC2742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2742 + difference 5 2) (sourceB2742 + difference 2 5) sourceC2742) = raw37730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2742 sourceB2742 sourceC2742 difference raw37730; decide +kernel
    rw [ha]
    exact (canonical37730 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2742 + sourceB2742) sourceC2742) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2742 + sourceB2742) sourceC2742) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2742 sourceB2742 sourceC2742 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2742 sourceB2742 sourceC2742
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2742, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2743 + difference 0 4) (sourceB2743 + difference 4 0) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2743 + difference 0 4) (sourceB2743 + difference 4 0) sourceC2743) = raw37731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37731; decide +kernel
    rw [ha]
    exact (canonical37731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2743 + difference 1 4) (sourceB2743 + difference 4 1) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2743 + difference 1 4) (sourceB2743 + difference 4 1) sourceC2743) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2743 + difference 2 4) (sourceB2743 + difference 4 2) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2743 + difference 2 4) (sourceB2743 + difference 4 2) sourceC2743) = raw37732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37732; decide +kernel
    rw [ha]
    exact (canonical37732 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2743 + difference 3 4) (sourceB2743 + difference 4 3) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2743 + difference 3 4) (sourceB2743 + difference 4 3) sourceC2743) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2743 + difference 4 4) (sourceB2743 + difference 4 4) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2743 + difference 4 4) (sourceB2743 + difference 4 4) sourceC2743) = raw37734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37734; decide +kernel
    rw [ha]
    exact (canonical37734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2743 + difference 5 4) (sourceB2743 + difference 4 5) sourceC2743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2743 + difference 5 4) (sourceB2743 + difference 4 5) sourceC2743) = raw37735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2743 sourceB2743 sourceC2743 difference raw37735; decide +kernel
    rw [ha]
    exact (canonical37735 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2743 + sourceB2743) sourceC2743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2743 + sourceB2743) sourceC2743) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2743 sourceB2743 sourceC2743 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2743 sourceB2743 sourceC2743
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2743, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2744 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2744 + difference 0 4) (sourceB2744 + difference 4 0) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2744 + difference 0 4) (sourceB2744 + difference 4 0) sourceC2744) = raw37736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37736; decide +kernel
    rw [ha]
    exact (canonical37736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2744 + difference 1 4) (sourceB2744 + difference 4 1) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2744 + difference 1 4) (sourceB2744 + difference 4 1) sourceC2744) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2744 + difference 2 4) (sourceB2744 + difference 4 2) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2744 + difference 2 4) (sourceB2744 + difference 4 2) sourceC2744) = raw37737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37737; decide +kernel
    rw [ha]
    exact (canonical37737 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2744 + difference 3 4) (sourceB2744 + difference 4 3) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2744 + difference 3 4) (sourceB2744 + difference 4 3) sourceC2744) = raw37738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37738; decide +kernel
    rw [ha]
    exact (canonical37738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2744 + difference 4 4) (sourceB2744 + difference 4 4) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2744 + difference 4 4) (sourceB2744 + difference 4 4) sourceC2744) = raw37739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37739; decide +kernel
    rw [ha]
    exact (canonical37739 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2744 + difference 5 4) (sourceB2744 + difference 4 5) sourceC2744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2744 + difference 5 4) (sourceB2744 + difference 4 5) sourceC2744) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2744 sourceB2744 sourceC2744 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2744 + sourceB2744) sourceC2744) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2744 + sourceB2744) sourceC2744) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2744 sourceB2744 sourceC2744 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2744 sourceB2744 sourceC2744
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2744, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2745 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2745 + difference 0 2) (sourceB2745 + difference 2 0) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2745 + difference 0 2) (sourceB2745 + difference 2 0) sourceC2745) = raw37740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37740; decide +kernel
    rw [ha]
    exact (canonical37740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2745 + difference 1 2) (sourceB2745 + difference 2 1) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2745 + difference 1 2) (sourceB2745 + difference 2 1) sourceC2745) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2745 + difference 2 2) (sourceB2745 + difference 2 2) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2745 + difference 2 2) (sourceB2745 + difference 2 2) sourceC2745) = raw37741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37741; decide +kernel
    rw [ha]
    exact (canonical37741 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2745 + difference 3 2) (sourceB2745 + difference 2 3) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2745 + difference 3 2) (sourceB2745 + difference 2 3) sourceC2745) = raw37742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37742; decide +kernel
    rw [ha]
    exact (canonical37742 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2745 + difference 4 2) (sourceB2745 + difference 2 4) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2745 + difference 4 2) (sourceB2745 + difference 2 4) sourceC2745) = raw37735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37735; decide +kernel
    rw [ha]
    exact (canonical37735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2745 + difference 5 2) (sourceB2745 + difference 2 5) sourceC2745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2745 + difference 5 2) (sourceB2745 + difference 2 5) sourceC2745) = raw37743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2745 sourceB2745 sourceC2745 difference raw37743; decide +kernel
    rw [ha]
    exact (canonical37743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2745 + sourceB2745) sourceC2745) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2745 + sourceB2745) sourceC2745) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2745 sourceB2745 sourceC2745 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2745 sourceB2745 sourceC2745
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2745, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2747 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 0) (sourceB2747 + difference 0 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 0) (sourceB2747 + difference 0 2) sourceC2747) = raw37730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37730; decide +kernel
    rw [ha]
    exact (canonical37730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 1) (sourceB2747 + difference 1 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 1) (sourceB2747 + difference 1 2) sourceC2747) = raw37743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37743; decide +kernel
    rw [ha]
    exact (canonical37743 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 2) (sourceB2747 + difference 2 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 2) (sourceB2747 + difference 2 2) sourceC2747) = raw37747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37747; decide +kernel
    rw [ha]
    exact (canonical37747 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 3) (sourceB2747 + difference 3 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 3) (sourceB2747 + difference 3 2) sourceC2747) = raw37748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37748; decide +kernel
    rw [ha]
    exact (canonical37748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 4) (sourceB2747 + difference 4 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 4) (sourceB2747 + difference 4 2) sourceC2747) = raw37749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37749; decide +kernel
    rw [ha]
    exact (canonical37749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2747 + difference 2 5) (sourceB2747 + difference 5 2) sourceC2747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2747 + difference 2 5) (sourceB2747 + difference 5 2) sourceC2747) = raw37726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2747 sourceB2747 sourceC2747 difference raw37726; decide +kernel
    rw [ha]
    exact (canonical37726 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2747 + sourceB2747) sourceC2747) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2747 + sourceB2747) sourceC2747) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2747 sourceB2747 sourceC2747 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2747 sourceB2747 sourceC2747
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2747, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2144 : Integer.Sparse.reindex keyMap MixedData.row2144 = numericRow2144 := by decide +kernel

theorem numericCheck2144 (x : Master → ℝ) : Integer.Sparse.eval numericRow2144 x =
    (1 : ℝ) * reducedSource2144 x := by
  norm_num [numericRow2144, reducedSource2144, Integer.Sparse.eval, Sparse.eval, nodeValue1690, nodeValue2184, nodeValue3255, nodeValue3264, nodeValue3273, nodeValue4064]

theorem reindexCheck2145 : Integer.Sparse.reindex keyMap MixedData.row2145 = numericRow2145 := by decide +kernel

theorem numericCheck2145 (x : Master → ℝ) : Integer.Sparse.eval numericRow2145 x =
    (1 : ℝ) * reducedSource2145 x := by
  norm_num [numericRow2145, reducedSource2145, Integer.Sparse.eval, Sparse.eval, nodeValue1681, nodeValue2657, nodeValue3258, nodeValue3265, nodeValue3270, nodeValue4065]

theorem reindexCheck2146 : Integer.Sparse.reindex keyMap MixedData.row2146 = numericRow2146 := by decide +kernel

theorem numericCheck2146 (x : Master → ℝ) : Integer.Sparse.eval numericRow2146 x =
    (1 : ℝ) * reducedSource2146 x := by
  norm_num [numericRow2146, reducedSource2146, Integer.Sparse.eval, Sparse.eval, nodeValue1691, nodeValue3261, nodeValue3265, nodeValue3274, nodeValue4065]

theorem reindexCheck2147 : Integer.Sparse.reindex keyMap MixedData.row2147 = numericRow2147 := by decide +kernel

theorem numericCheck2147 (x : Master → ℝ) : Integer.Sparse.eval numericRow2147 x =
    (1 : ℝ) * reducedSource2147 x := by
  norm_num [numericRow2147, reducedSource2147, Integer.Sparse.eval, Sparse.eval, nodeValue2161, nodeValue2163, nodeValue2169, nodeValue4076]

theorem reindexCheck2148 : Integer.Sparse.reindex keyMap MixedData.row2148 = numericRow2148 := by decide +kernel

theorem numericCheck2148 (x : Master → ℝ) : Integer.Sparse.eval numericRow2148 x =
    (1 : ℝ) * reducedSource2148 x := by
  norm_num [numericRow2148, reducedSource2148, Integer.Sparse.eval, Sparse.eval, nodeValue2155, nodeValue2159, nodeValue2168, nodeValue2273, nodeValue3596, nodeValue4076]

theorem reindexCheck2149 : Integer.Sparse.reindex keyMap MixedData.row2149 = numericRow2149 := by decide +kernel

theorem numericCheck2149 (x : Master → ℝ) : Integer.Sparse.eval numericRow2149 x =
    (1 : ℝ) * reducedSource2149 x := by
  norm_num [numericRow2149, reducedSource2149, Integer.Sparse.eval, Sparse.eval, nodeValue2164, nodeValue2168, nodeValue2169, nodeValue2286, nodeValue3423, nodeValue4076]

theorem reindexCheck2150 : Integer.Sparse.reindex keyMap MixedData.row2150 = numericRow2150 := by decide +kernel

theorem numericCheck2150 (x : Master → ℝ) : Integer.Sparse.eval numericRow2150 x =
    (1 : ℝ) * reducedSource2150 x := by
  norm_num [numericRow2150, reducedSource2150, Integer.Sparse.eval, Sparse.eval, nodeValue2168, nodeValue3415, nodeValue3422, nodeValue3423, nodeValue3596, nodeValue4076]

theorem reindexCheck2151 : Integer.Sparse.reindex keyMap MixedData.row2151 = numericRow2151 := by decide +kernel

theorem numericCheck2151 (x : Master → ℝ) : Integer.Sparse.eval numericRow2151 x =
    (1 : ℝ) * reducedSource2151 x := by
  norm_num [numericRow2151, reducedSource2151, Integer.Sparse.eval, Sparse.eval, nodeValue3419, nodeValue3422, nodeValue3423, nodeValue4076]

theorem reindexCheck2152 : Integer.Sparse.reindex keyMap MixedData.row2152 = numericRow2152 := by decide +kernel

theorem numericCheck2152 (x : Master → ℝ) : Integer.Sparse.eval numericRow2152 x =
    (1 : ℝ) * reducedSource2152 x := by
  norm_num [numericRow2152, reducedSource2152, Integer.Sparse.eval, Sparse.eval, nodeValue2169, nodeValue3423, nodeValue3512, nodeValue4076]

theorem reindexCheck2153 : Integer.Sparse.reindex keyMap MixedData.row2153 = numericRow2153 := by decide +kernel

theorem numericCheck2153 (x : Master → ℝ) : Integer.Sparse.eval numericRow2153 x =
    (1 : ℝ) * reducedSource2153 x := by
  norm_num [numericRow2153, reducedSource2153, Integer.Sparse.eval, Sparse.eval, nodeValue2147, nodeValue2151, nodeValue2153, nodeValue2165, nodeValue2256, nodeValue3457, nodeValue4074]

theorem reindexCheck2154 : Integer.Sparse.reindex keyMap MixedData.row2154 = numericRow2154 := by decide +kernel

theorem numericCheck2154 (x : Master → ℝ) : Integer.Sparse.eval numericRow2154 x =
    (1 : ℝ) * reducedSource2154 x := by
  norm_num [numericRow2154, reducedSource2154, Integer.Sparse.eval, Sparse.eval, nodeValue2160, nodeValue2162, nodeValue2165, nodeValue2180, nodeValue2186, nodeValue4074]

theorem reindexCheck2155 : Integer.Sparse.reindex keyMap MixedData.row2155 = numericRow2155 := by decide +kernel

theorem numericCheck2155 (x : Master → ℝ) : Integer.Sparse.eval numericRow2155 x =
    (1 : ℝ) * reducedSource2155 x := by
  norm_num [numericRow2155, reducedSource2155, Integer.Sparse.eval, Sparse.eval, nodeValue2140, nodeValue2143, nodeValue2151, nodeValue2239, nodeValue3588, nodeValue4074]

theorem reindexCheck2156 : Integer.Sparse.reindex keyMap MixedData.row2156 = numericRow2156 := by decide +kernel

theorem numericCheck2156 (x : Master → ℝ) : Integer.Sparse.eval numericRow2156 x =
    (1 : ℝ) * reducedSource2156 x := by
  norm_num [numericRow2156, reducedSource2156, Integer.Sparse.eval, Sparse.eval, nodeValue3408, nodeValue3411, nodeValue3413, nodeValue3420, nodeValue3457, nodeValue4074]

theorem reindexCheck2157 : Integer.Sparse.reindex keyMap MixedData.row2157 = numericRow2157 := by decide +kernel

theorem numericCheck2157 (x : Master → ℝ) : Integer.Sparse.eval numericRow2157 x =
    (1 : ℝ) * reducedSource2157 x := by
  norm_num [numericRow2157, reducedSource2157, Integer.Sparse.eval, Sparse.eval, nodeValue2181, nodeValue2185, nodeValue2186, nodeValue2223, nodeValue3420, nodeValue4074]

theorem reindexCheck2158 : Integer.Sparse.reindex keyMap MixedData.row2158 = numericRow2158 := by decide +kernel

theorem numericCheck2158 (x : Master → ℝ) : Integer.Sparse.eval numericRow2158 x =
    (1 : ℝ) * reducedSource2158 x := by
  norm_num [numericRow2158, reducedSource2158, Integer.Sparse.eval, Sparse.eval, nodeValue2185, nodeValue3403, nodeValue3411, nodeValue3420, nodeValue3588, nodeValue4074]

theorem reindexCheck2159 : Integer.Sparse.reindex keyMap MixedData.row2159 = numericRow2159 := by decide +kernel

theorem numericCheck2159 (x : Master → ℝ) : Integer.Sparse.eval numericRow2159 x =
    (1 : ℝ) * reducedSource2159 x := by
  norm_num [numericRow2159, reducedSource2159, Integer.Sparse.eval, Sparse.eval, nodeValue2143, nodeValue2176, nodeValue2185, nodeValue2212, nodeValue3588, nodeValue4074]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2144 (mixedVector B) = 0 := by
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  simpa only [sourceForm2720, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1690, h2184, h3255, h3264, h3273, h4064, reducedSource2144] using sourceEq2720 B hB

theorem rowSound2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2144 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2144, numericCheck2144, reducedZero2144 B hB hF, mul_zero]

theorem reducedZero2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2145 (mixedVector B) = 0 := by
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3270 : mixedVector B (Sum.inr 3270) = Sparse.eval nodeValue3270 (mixedVector B) := by
    change mixedMoment B node3270 node3270Labels = _
    exact sound3270 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  simpa only [sourceForm2725, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1681, h2657, h3258, h3265, h3270, h4065, reducedSource2145] using sourceEq2725 B hB

theorem rowSound2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2145, numericCheck2145, reducedZero2145 B hB hF, mul_zero]

theorem reducedZero2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2146 (mixedVector B) = 0 := by
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3274 : mixedVector B (Sum.inr 3274) = Sparse.eval nodeValue3274 (mixedVector B) := by
    change mixedMoment B node3274 node3274Labels = _
    exact sound3274 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  simpa only [sourceForm2726, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1691, h3261, h3265, h3274, h4065, reducedSource2146] using sourceEq2726 B hB

theorem rowSound2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2146, numericCheck2146, reducedZero2146 B hB hF, mul_zero]

theorem reducedZero2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2147 (mixedVector B) = 0 := by
  have h2161 : mixedVector B (Sum.inr 2161) = Sparse.eval nodeValue2161 (mixedVector B) := by
    change mixedMoment B node2161 node2161Labels = _
    exact sound2161 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2728, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2161, h2163, h2169, h4076, reducedSource2147] using sourceEq2728 B hB

theorem rowSound2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2147, numericCheck2147, reducedZero2147 B hB hF, mul_zero]

theorem reducedZero2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2148 (mixedVector B) = 0 := by
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2729, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2155, h2159, h2168, h2273, h3596, h4076, reducedSource2148] using sourceEq2729 B hB

theorem rowSound2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2148, numericCheck2148, reducedZero2148 B hB hF, mul_zero]

theorem reducedZero2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2149 (mixedVector B) = 0 := by
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2730, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2164, h2168, h2169, h2286, h3423, h4076, reducedSource2149] using sourceEq2730 B hB

theorem rowSound2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2149, numericCheck2149, reducedZero2149 B hB hF, mul_zero]

theorem reducedZero2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2150 (mixedVector B) = 0 := by
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2731, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2168, h3415, h3422, h3423, h3596, h4076, reducedSource2150] using sourceEq2731 B hB

theorem rowSound2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2150, numericCheck2150, reducedZero2150 B hB hF, mul_zero]

theorem reducedZero2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2151 (mixedVector B) = 0 := by
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3422 : mixedVector B (Sum.inr 3422) = Sparse.eval nodeValue3422 (mixedVector B) := by
    change mixedMoment B node3422 node3422Labels = _
    exact sound3422 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2732, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3419, h3422, h3423, h4076, reducedSource2151] using sourceEq2732 B hB

theorem rowSound2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2151 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2151, numericCheck2151, reducedZero2151 B hB hF, mul_zero]

theorem reducedZero2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2152 (mixedVector B) = 0 := by
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  simpa only [sourceForm2733, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2169, h3423, h3512, h4076, reducedSource2152] using sourceEq2733 B hB

theorem rowSound2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2152, numericCheck2152, reducedZero2152 B hB hF, mul_zero]

theorem reducedZero2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2153 (mixedVector B) = 0 := by
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2740, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2147, h2151, h2153, h2165, h2256, h3457, h4074, reducedSource2153] using sourceEq2740 B hB

theorem rowSound2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2153 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2153, numericCheck2153, reducedZero2153 B hB hF, mul_zero]

theorem reducedZero2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2154 (mixedVector B) = 0 := by
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2180 : mixedVector B (Sum.inr 2180) = Sparse.eval nodeValue2180 (mixedVector B) := by
    change mixedMoment B node2180 node2180Labels = _
    exact sound2180 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2160, h2162, h2165, h2180, h2186, h4074, reducedSource2154] using sourceEq2741 B hB

theorem rowSound2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2154, numericCheck2154, reducedZero2154 B hB hF, mul_zero]

theorem reducedZero2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2155 (mixedVector B) = 0 := by
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2742, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2140, h2143, h2151, h2239, h3588, h4074, reducedSource2155] using sourceEq2742 B hB

theorem rowSound2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2155, numericCheck2155, reducedZero2155 B hB hF, mul_zero]

theorem reducedZero2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2156 (mixedVector B) = 0 := by
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3408, h3411, h3413, h3420, h3457, h4074, reducedSource2156] using sourceEq2743 B hB

theorem rowSound2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2156, numericCheck2156, reducedZero2156 B hB hF, mul_zero]

theorem reducedZero2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2157 (mixedVector B) = 0 := by
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2744, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2181, h2185, h2186, h2223, h3420, h4074, reducedSource2157] using sourceEq2744 B hB

theorem rowSound2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2157, numericCheck2157, reducedZero2157 B hB hF, mul_zero]

theorem reducedZero2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2158 (mixedVector B) = 0 := by
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2745, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2185, h3403, h3411, h3420, h3588, h4074, reducedSource2158] using sourceEq2745 B hB

theorem rowSound2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2158, numericCheck2158, reducedZero2158 B hB hF, mul_zero]

theorem reducedZero2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2159 (mixedVector B) = 0 := by
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2747, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2143, h2176, h2185, h2212, h3588, h4074, reducedSource2159] using sourceEq2747 B hB

theorem rowSound2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2159 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2159, numericCheck2159, reducedZero2159 B hB hF, mul_zero]

theorem sourceRowsAt2144 : MixedData.sourceRows (2144 : Fin 2425) =
    MixedData.row2144 := by decide +kernel

theorem sourceRowsAt2145 : MixedData.sourceRows (2145 : Fin 2425) =
    MixedData.row2145 := by decide +kernel

theorem sourceRowsAt2146 : MixedData.sourceRows (2146 : Fin 2425) =
    MixedData.row2146 := by decide +kernel

theorem sourceRowsAt2147 : MixedData.sourceRows (2147 : Fin 2425) =
    MixedData.row2147 := by decide +kernel

theorem sourceRowsAt2148 : MixedData.sourceRows (2148 : Fin 2425) =
    MixedData.row2148 := by decide +kernel

theorem sourceRowsAt2149 : MixedData.sourceRows (2149 : Fin 2425) =
    MixedData.row2149 := by decide +kernel

theorem sourceRowsAt2150 : MixedData.sourceRows (2150 : Fin 2425) =
    MixedData.row2150 := by decide +kernel

theorem sourceRowsAt2151 : MixedData.sourceRows (2151 : Fin 2425) =
    MixedData.row2151 := by decide +kernel

theorem sourceRowsAt2152 : MixedData.sourceRows (2152 : Fin 2425) =
    MixedData.row2152 := by decide +kernel

theorem sourceRowsAt2153 : MixedData.sourceRows (2153 : Fin 2425) =
    MixedData.row2153 := by decide +kernel

theorem sourceRowsAt2154 : MixedData.sourceRows (2154 : Fin 2425) =
    MixedData.row2154 := by decide +kernel

theorem sourceRowsAt2155 : MixedData.sourceRows (2155 : Fin 2425) =
    MixedData.row2155 := by decide +kernel

theorem sourceRowsAt2156 : MixedData.sourceRows (2156 : Fin 2425) =
    MixedData.row2156 := by decide +kernel

theorem sourceRowsAt2157 : MixedData.sourceRows (2157 : Fin 2425) =
    MixedData.row2157 := by decide +kernel

theorem sourceRowsAt2158 : MixedData.sourceRows (2158 : Fin 2425) =
    MixedData.row2158 := by decide +kernel

theorem sourceRowsAt2159 : MixedData.sourceRows (2159 : Fin 2425) =
    MixedData.row2159 := by decide +kernel

theorem chunkSound134_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 134) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2144 ∨ k.val = 2145 ∨ k.val = 2146 ∨ k.val = 2147 ∨ k.val = 2148 ∨ k.val = 2149 ∨ k.val = 2150 ∨ k.val = 2151 ∨ k.val = 2152 ∨ k.val = 2153 ∨ k.val = 2154 ∨ k.val = 2155 ∨ k.val = 2156 ∨ k.val = 2157 ∨ k.val = 2158 ∨ k.val = 2159 := by omega
  rcases heq with h2144 | h2145 | h2146 | h2147 | h2148 | h2149 | h2150 | h2151 | h2152 | h2153 | h2154 | h2155 | h2156 | h2157 | h2158 | h2159
  · have he : k = (2144 : Fin 2425) := Fin.ext h2144
    subst k
    rw [sourceRowsAt2144]
    exact rowSound2144 B hB hF
  · have he : k = (2145 : Fin 2425) := Fin.ext h2145
    subst k
    rw [sourceRowsAt2145]
    exact rowSound2145 B hB hF
  · have he : k = (2146 : Fin 2425) := Fin.ext h2146
    subst k
    rw [sourceRowsAt2146]
    exact rowSound2146 B hB hF
  · have he : k = (2147 : Fin 2425) := Fin.ext h2147
    subst k
    rw [sourceRowsAt2147]
    exact rowSound2147 B hB hF
  · have he : k = (2148 : Fin 2425) := Fin.ext h2148
    subst k
    rw [sourceRowsAt2148]
    exact rowSound2148 B hB hF
  · have he : k = (2149 : Fin 2425) := Fin.ext h2149
    subst k
    rw [sourceRowsAt2149]
    exact rowSound2149 B hB hF
  · have he : k = (2150 : Fin 2425) := Fin.ext h2150
    subst k
    rw [sourceRowsAt2150]
    exact rowSound2150 B hB hF
  · have he : k = (2151 : Fin 2425) := Fin.ext h2151
    subst k
    rw [sourceRowsAt2151]
    exact rowSound2151 B hB hF
  · have he : k = (2152 : Fin 2425) := Fin.ext h2152
    subst k
    rw [sourceRowsAt2152]
    exact rowSound2152 B hB hF
  · have he : k = (2153 : Fin 2425) := Fin.ext h2153
    subst k
    rw [sourceRowsAt2153]
    exact rowSound2153 B hB hF
  · have he : k = (2154 : Fin 2425) := Fin.ext h2154
    subst k
    rw [sourceRowsAt2154]
    exact rowSound2154 B hB hF
  · have he : k = (2155 : Fin 2425) := Fin.ext h2155
    subst k
    rw [sourceRowsAt2155]
    exact rowSound2155 B hB hF
  · have he : k = (2156 : Fin 2425) := Fin.ext h2156
    subst k
    rw [sourceRowsAt2156]
    exact rowSound2156 B hB hF
  · have he : k = (2157 : Fin 2425) := Fin.ext h2157
    subst k
    rw [sourceRowsAt2157]
    exact rowSound2157 B hB hF
  · have he : k = (2158 : Fin 2425) := Fin.ext h2158
    subst k
    rw [sourceRowsAt2158]
    exact rowSound2158 B hB hF
  · have he : k = (2159 : Fin 2425) := Fin.ext h2159
    subst k
    rw [sourceRowsAt2159]
    exact rowSound2159 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e_oai
