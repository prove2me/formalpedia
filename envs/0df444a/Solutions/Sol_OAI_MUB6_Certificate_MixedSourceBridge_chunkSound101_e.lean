-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:28.523096+00:00
-- url     : https://prove2.me/submissions/51098bd7-4c2c-4f6e-8f82-7d0171b63381

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23023 raw23023Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23023 raw23023Labels = mixedMoment B raw23023step0 raw23023step0Labels := by
      have hz : ∀ j, raw23023 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23023step0 = (fun i j => raw23023 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23023step0 raw23023; decide +kernel
      have hl : raw23023step0Labels = raw23023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023 raw23023Labels permutation590 hz
    mixedMoment B raw23023step0 raw23023step0Labels = mixedMoment B raw23023step1 raw23023step1Labels := by
      have hz : ∀ j, raw23023step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23023step1 = (fun i j => raw23023step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23023step1 raw23023step0; decide +kernel
      have hl : raw23023step1Labels = raw23023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step0 raw23023step0Labels permutation104 hz
    mixedMoment B raw23023step1 raw23023step1Labels = mixedMoment B raw23023step2 raw23023step2Labels := by
      have hz : ∀ j, raw23023step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw23023step2 = (fun i j => raw23023step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw23023step2 raw23023step1; decide +kernel
      have hl : raw23023step2Labels = raw23023step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step1 raw23023step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23028 raw23028Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw23028 raw23028Labels = mixedMoment B raw23028step0 raw23028step0Labels := by
      have hz : ∀ j, raw23028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23028step0 = (fun i j => raw23028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23028step0 raw23028; decide +kernel
      have hl : raw23028step0Labels = raw23028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028 raw23028Labels permutation434 hz
    mixedMoment B raw23028step0 raw23028step0Labels = mixedMoment B raw23028step1 raw23028step1Labels := by
      have hz : ∀ j, raw23028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23028step1 = (fun i j => raw23028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23028step1 raw23028step0; decide +kernel
      have hl : raw23028step1Labels = raw23028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028step0 raw23028step0Labels permutation80 hz
    mixedMoment B raw23028step1 raw23028step1Labels = mixedMoment B raw23028step2 raw23028step2Labels := by
      have ha : raw23028step2 = (fun i j => raw23028step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23028step2 raw23028step1; decide +kernel
      have hl : raw23028step2Labels = raw23028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23028step1 raw23028step1Labels permutation9 permutation2
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical23032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23032 raw23032Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw23032 raw23032Labels = mixedMoment B raw23032step0 raw23032step0Labels := by
      have hz : ∀ j, raw23032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23032step0 = (fun i j => raw23032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23032step0 raw23032; decide +kernel
      have hl : raw23032step0Labels = raw23032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032 raw23032Labels permutation434 hz
    mixedMoment B raw23032step0 raw23032step0Labels = mixedMoment B raw23032step1 raw23032step1Labels := by
      have hz : ∀ j, raw23032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23032step1 = (fun i j => raw23032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23032step1 raw23032step0; decide +kernel
      have hl : raw23032step1Labels = raw23032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032step0 raw23032step0Labels permutation80 hz
    _ = mixedMoment B node954 node954Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25231 raw25231Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25231 raw25231Labels = mixedMoment B raw25231step0 raw25231step0Labels := by
      have hz : ∀ j, raw25231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25231step0 = (fun i j => raw25231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25231step0 raw25231; decide +kernel
      have hl : raw25231step0Labels = raw25231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231 raw25231Labels permutation520 hz
    mixedMoment B raw25231step0 raw25231step0Labels = mixedMoment B raw25231step1 raw25231step1Labels := by
      have hz : ∀ j, raw25231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25231step1 = (fun i j => raw25231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25231step1 raw25231step0; decide +kernel
      have hl : raw25231step1Labels = raw25231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231step0 raw25231step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25236 raw25236Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw25236 raw25236Labels = mixedMoment B raw25236step0 raw25236step0Labels := by
      have hz : ∀ j, raw25236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25236step0 = (fun i j => raw25236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25236step0 raw25236; decide +kernel
      have hl : raw25236step0Labels = raw25236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25236 raw25236Labels permutation346 hz
    mixedMoment B raw25236step0 raw25236step0Labels = mixedMoment B raw25236step1 raw25236step1Labels := by
      have ha : raw25236step1 = (fun i j => raw25236step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25236step1 raw25236step0; decide +kernel
      have hl : raw25236step1Labels = raw25236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25236step0 raw25236step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical25240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25240 raw25240Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw25240 raw25240Labels = mixedMoment B raw25240step0 raw25240step0Labels := by
      have hz : ∀ j, raw25240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25240step0 = (fun i j => raw25240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25240step0 raw25240; decide +kernel
      have hl : raw25240step0Labels = raw25240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25240 raw25240Labels permutation346 hz
    mixedMoment B raw25240step0 raw25240step0Labels = mixedMoment B raw25240step1 raw25240step1Labels := by
      have ha : raw25240step1 = (fun i j => raw25240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25240step1 raw25240step0; decide +kernel
      have hl : raw25240step1Labels = raw25240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25240step0 raw25240step0Labels permutation34 permutation2
    _ = mixedMoment B node945 node945Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27357 raw27357Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw27357 raw27357Labels = mixedMoment B raw27357step0 raw27357step0Labels := by
      have hz : ∀ j, raw27357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27357step0 = (fun i j => raw27357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27357step0 raw27357; decide +kernel
      have hl : raw27357step0Labels = raw27357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27357 raw27357Labels permutation346 hz
    mixedMoment B raw27357step0 raw27357step0Labels = mixedMoment B raw27357step1 raw27357step1Labels := by
      have ha : raw27357step1 = (fun i j => raw27357step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27357step1 raw27357step0; decide +kernel
      have hl : raw27357step1Labels = raw27357step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27357step0 raw27357step0Labels permutation148 permutation2
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical27359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27359 raw27359Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27359 raw27359Labels = mixedMoment B raw27359step0 raw27359step0Labels := by
      have hz : ∀ j, raw27359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27359step0 = (fun i j => raw27359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27359step0 raw27359; decide +kernel
      have hl : raw27359step0Labels = raw27359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27359 raw27359Labels permutation346 hz
    mixedMoment B raw27359step0 raw27359step0Labels = mixedMoment B raw27359step1 raw27359step1Labels := by
      have ha : raw27359step1 = (fun i j => raw27359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27359step1 raw27359step0; decide +kernel
      have hl : raw27359step1Labels = raw27359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27359step0 raw27359step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27366 raw27366Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27366 raw27366Labels = mixedMoment B raw27366step0 raw27366step0Labels := by
      have hz : ∀ j, raw27366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27366step0 = (fun i j => raw27366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27366step0 raw27366; decide +kernel
      have hl : raw27366step0Labels = raw27366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27366 raw27366Labels permutation346 hz
    mixedMoment B raw27366step0 raw27366step0Labels = mixedMoment B raw27366step1 raw27366step1Labels := by
      have ha : raw27366step1 = (fun i j => raw27366step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27366step1 raw27366step0; decide +kernel
      have hl : raw27366step1Labels = raw27366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27366step0 raw27366step0Labels permutation44 permutation4
    mixedMoment B raw27366step1 raw27366step1Labels = mixedMoment B raw27366step2 raw27366step2Labels := by
      have ha : raw27366step2 = -raw27366step1 := by apply Matrix.ext; change ∀ i j, raw27366step2 i j = -(raw27366step1 i j); unfold raw27366step2 raw27366step1; decide +kernel
      have hl : raw27366step2Labels = raw27366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27378 raw27378Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw27378 raw27378Labels = mixedMoment B raw27378step0 raw27378step0Labels := by
      have ha : raw27378step0 = (fun i j => raw27378 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27378step0 raw27378; decide +kernel
      have hl : raw27378step0Labels = raw27378Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27378 raw27378Labels permutation674 permutation2
    _ = mixedMoment B node3466 node3466Labels := by rfl

theorem canonical27388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27388 raw27388Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw27388 raw27388Labels = mixedMoment B raw27388step0 raw27388step0Labels := by
      have ha : raw27388step0 = (fun i j => raw27388 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27388step0 raw27388; decide +kernel
      have hl : raw27388step0Labels = raw27388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27388 raw27388Labels permutation682 permutation2
    mixedMoment B raw27388step0 raw27388step0Labels = mixedMoment B raw27388step1 raw27388step1Labels := by
      have ha : raw27388step1 = -raw27388step0 := by apply Matrix.ext; change ∀ i j, raw27388step1 i j = -(raw27388step0 i j); unfold raw27388step1 raw27388step0; decide +kernel
      have hl : raw27388step1Labels = raw27388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

theorem canonical27389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27389 raw27389Labels = mixedMoment B node1904 node1904Labels := by
  calc
    mixedMoment B raw27389 raw27389Labels = mixedMoment B raw27389step0 raw27389step0Labels := by
      have ha : raw27389step0 = (fun i j => raw27389 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27389step0 raw27389; decide +kernel
      have hl : raw27389step0Labels = raw27389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27389 raw27389Labels permutation681 permutation2
    mixedMoment B raw27389step0 raw27389step0Labels = mixedMoment B raw27389step1 raw27389step1Labels := by
      have ha : raw27389step1 = -raw27389step0 := by apply Matrix.ext; change ∀ i j, raw27389step1 i j = -(raw27389step0 i j); unfold raw27389step1 raw27389step0; decide +kernel
      have hl : raw27389step1Labels = raw27389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1904 node1904Labels := by rfl

theorem canonical27390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27390 raw27390Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw27390 raw27390Labels = mixedMoment B raw27390step0 raw27390step0Labels := by
      have ha : raw27390step0 = (fun i j => raw27390 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27390step0 raw27390; decide +kernel
      have hl : raw27390step0Labels = raw27390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27390 raw27390Labels permutation686 permutation2
    mixedMoment B raw27390step0 raw27390step0Labels = mixedMoment B raw27390step1 raw27390step1Labels := by
      have ha : raw27390step1 = -raw27390step0 := by apply Matrix.ext; change ∀ i j, raw27390step1 i j = -(raw27390step0 i j); unfold raw27390step1 raw27390step0; decide +kernel
      have hl : raw27390step1Labels = raw27390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical27391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27391 raw27391Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw27391 raw27391Labels = mixedMoment B raw27391step0 raw27391step0Labels := by
      have ha : raw27391step0 = (fun i j => raw27391 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27391step0 raw27391; decide +kernel
      have hl : raw27391step0Labels = raw27391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27391 raw27391Labels permutation680 permutation2
    mixedMoment B raw27391step0 raw27391step0Labels = mixedMoment B raw27391step1 raw27391step1Labels := by
      have ha : raw27391step1 = -raw27391step0 := by apply Matrix.ext; change ∀ i j, raw27391step1 i j = -(raw27391step0 i j); unfold raw27391step1 raw27391step0; decide +kernel
      have hl : raw27391step1Labels = raw27391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1913 node1913Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27392 raw27392Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw27392 raw27392Labels = mixedMoment B raw27392step0 raw27392step0Labels := by
      have ha : raw27392step0 = (fun i j => raw27392 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27392step0 raw27392; decide +kernel
      have hl : raw27392step0Labels = raw27392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27392 raw27392Labels permutation682 permutation2
    mixedMoment B raw27392step0 raw27392step0Labels = mixedMoment B raw27392step1 raw27392step1Labels := by
      have ha : raw27392step1 = -raw27392step0 := by apply Matrix.ext; change ∀ i j, raw27392step1 i j = -(raw27392step0 i j); unfold raw27392step1 raw27392step0; decide +kernel
      have hl : raw27392step1Labels = raw27392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical27393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27393 raw27393Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw27393 raw27393Labels = mixedMoment B raw27393step0 raw27393step0Labels := by
      have ha : raw27393step0 = (fun i j => raw27393 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27393step0 raw27393; decide +kernel
      have hl : raw27393step0Labels = raw27393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27393 raw27393Labels permutation682 permutation2
    mixedMoment B raw27393step0 raw27393step0Labels = mixedMoment B raw27393step1 raw27393step1Labels := by
      have ha : raw27393step1 = -raw27393step0 := by apply Matrix.ext; change ∀ i j, raw27393step1 i j = -(raw27393step0 i j); unfold raw27393step1 raw27393step0; decide +kernel
      have hl : raw27393step1Labels = raw27393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical27394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27394 raw27394Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27394 raw27394Labels = mixedMoment B raw27394step0 raw27394step0Labels := by
      have hz : ∀ j, raw27394 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw27394step0 = (fun i j => raw27394 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw27394step0 raw27394; decide +kernel
      have hl : raw27394step0Labels = raw27394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27394 raw27394Labels permutation152 hz
    mixedMoment B raw27394step0 raw27394step0Labels = mixedMoment B raw27394step1 raw27394step1Labels := by
      have ha : raw27394step1 = (fun i j => raw27394step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27394step1 raw27394step0; decide +kernel
      have hl : raw27394step1Labels = raw27394step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27394step0 raw27394step0Labels permutation146 permutation0
    mixedMoment B raw27394step1 raw27394step1Labels = mixedMoment B raw27394step2 raw27394step2Labels := by
      have ha : raw27394step2 = -raw27394step1 := by apply Matrix.ext; change ∀ i j, raw27394step2 i j = -(raw27394step1 i j); unfold raw27394step2 raw27394step1; decide +kernel
      have hl : raw27394step2Labels = raw27394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical27395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27395 raw27395Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw27395 raw27395Labels = mixedMoment B raw27395step0 raw27395step0Labels := by
      have hz : ∀ j, raw27395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27395step0 = (fun i j => raw27395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27395step0 raw27395; decide +kernel
      have hl : raw27395step0Labels = raw27395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395 raw27395Labels permutation434 hz
    mixedMoment B raw27395step0 raw27395step0Labels = mixedMoment B raw27395step1 raw27395step1Labels := by
      have hz : ∀ j, raw27395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27395step1 = (fun i j => raw27395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27395step1 raw27395step0; decide +kernel
      have hl : raw27395step1Labels = raw27395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395step0 raw27395step0Labels permutation80 hz
    _ = mixedMoment B node1832 node1832Labels := by rfl

theorem canonical27396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27396 raw27396Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27396 raw27396Labels = mixedMoment B raw27396step0 raw27396step0Labels := by
      have hz : ∀ j, raw27396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27396step0 = (fun i j => raw27396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27396step0 raw27396; decide +kernel
      have hl : raw27396step0Labels = raw27396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27396 raw27396Labels permutation434 hz
    mixedMoment B raw27396step0 raw27396step0Labels = mixedMoment B raw27396step1 raw27396step1Labels := by
      have ha : raw27396step1 = (fun i j => raw27396step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27396step1 raw27396step0; decide +kernel
      have hl : raw27396step1Labels = raw27396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27396step0 raw27396step0Labels permutation38 permutation2
    _ = mixedMoment B node1980 node1980Labels := by rfl

theorem canonical27397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27397 raw27397Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27397 raw27397Labels = mixedMoment B raw27397step0 raw27397step0Labels := by
      have hz : ∀ j, raw27397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27397step0 = (fun i j => raw27397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27397step0 raw27397; decide +kernel
      have hl : raw27397step0Labels = raw27397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27397 raw27397Labels permutation346 hz
    mixedMoment B raw27397step0 raw27397step0Labels = mixedMoment B raw27397step1 raw27397step1Labels := by
      have ha : raw27397step1 = (fun i j => raw27397step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27397step1 raw27397step0; decide +kernel
      have hl : raw27397step1Labels = raw27397step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27397step0 raw27397step0Labels permutation38 permutation2
    _ = mixedMoment B node1980 node1980Labels := by rfl

theorem canonical27398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27398 raw27398Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw27398 raw27398Labels = mixedMoment B raw27398step0 raw27398step0Labels := by
      have hz : ∀ j, raw27398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27398step0 = (fun i j => raw27398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27398step0 raw27398; decide +kernel
      have hl : raw27398step0Labels = raw27398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27398 raw27398Labels permutation434 hz
    mixedMoment B raw27398step0 raw27398step0Labels = mixedMoment B raw27398step1 raw27398step1Labels := by
      have hz : ∀ j, raw27398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27398step1 = (fun i j => raw27398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27398step1 raw27398step0; decide +kernel
      have hl : raw27398step1Labels = raw27398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27398step0 raw27398step0Labels permutation80 hz
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical27399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27399 raw27399Labels = mixedMoment B node1825 node1825Labels := by
  calc
    mixedMoment B raw27399 raw27399Labels = mixedMoment B raw27399step0 raw27399step0Labels := by
      have hz : ∀ j, raw27399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27399step0 = (fun i j => raw27399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27399step0 raw27399; decide +kernel
      have hl : raw27399step0Labels = raw27399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27399 raw27399Labels permutation346 hz
    mixedMoment B raw27399step0 raw27399step0Labels = mixedMoment B raw27399step1 raw27399step1Labels := by
      have ha : raw27399step1 = (fun i j => raw27399step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27399step1 raw27399step0; decide +kernel
      have hl : raw27399step1Labels = raw27399step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27399step0 raw27399step0Labels permutation34 permutation2
    _ = mixedMoment B node1825 node1825Labels := by rfl

theorem canonical27400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27400 raw27400Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27400 raw27400Labels = mixedMoment B raw27400step0 raw27400step0Labels := by
      have ha : raw27400step0 = (fun i j => raw27400 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27400step0 raw27400; decide +kernel
      have hl : raw27400step0Labels = raw27400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27400 raw27400Labels permutation178 permutation2
    _ = mixedMoment B node1973 node1973Labels := by rfl

theorem canonical27401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27401 raw27401Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27401 raw27401Labels = mixedMoment B raw27401step0 raw27401step0Labels := by
      have hz : ∀ j, raw27401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27401step0 = (fun i j => raw27401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27401step0 raw27401; decide +kernel
      have hl : raw27401step0Labels = raw27401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27401 raw27401Labels permutation346 hz
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical27402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27402 raw27402Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw27402 raw27402Labels = mixedMoment B raw27402step0 raw27402step0Labels := by
      have hz : ∀ j, raw27402 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27402step0 = (fun i j => raw27402 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27402step0 raw27402; decide +kernel
      have hl : raw27402step0Labels = raw27402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27402 raw27402Labels permutation520 hz
    mixedMoment B raw27402step0 raw27402step0Labels = mixedMoment B raw27402step1 raw27402step1Labels := by
      have hz : ∀ j, raw27402step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27402step1 = (fun i j => raw27402step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27402step1 raw27402step0; decide +kernel
      have hl : raw27402step1Labels = raw27402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27402step0 raw27402step0Labels permutation80 hz
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical27403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27403 raw27403Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw27403 raw27403Labels = mixedMoment B raw27403step0 raw27403step0Labels := by
      have hz : ∀ j, raw27403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27403step0 = (fun i j => raw27403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27403step0 raw27403; decide +kernel
      have hl : raw27403step0Labels = raw27403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27403 raw27403Labels permutation346 hz
    mixedMoment B raw27403step0 raw27403step0Labels = mixedMoment B raw27403step1 raw27403step1Labels := by
      have ha : raw27403step1 = (fun i j => raw27403step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27403step1 raw27403step0; decide +kernel
      have hl : raw27403step1Labels = raw27403step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27403step0 raw27403step0Labels permutation150 permutation2
    mixedMoment B raw27403step1 raw27403step1Labels = mixedMoment B raw27403step2 raw27403step2Labels := by
      have ha : raw27403step2 = -raw27403step1 := by apply Matrix.ext; change ∀ i j, raw27403step2 i j = -(raw27403step1 i j); unfold raw27403step2 raw27403step1; decide +kernel
      have hl : raw27403step2Labels = raw27403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical27404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27404 raw27404Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw27404 raw27404Labels = mixedMoment B raw27404step0 raw27404step0Labels := by
      have hz : ∀ j, raw27404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27404step0 = (fun i j => raw27404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27404step0 raw27404; decide +kernel
      have hl : raw27404step0Labels = raw27404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27404 raw27404Labels permutation346 hz
    mixedMoment B raw27404step0 raw27404step0Labels = mixedMoment B raw27404step1 raw27404step1Labels := by
      have ha : raw27404step1 = (fun i j => raw27404step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27404step1 raw27404step0; decide +kernel
      have hl : raw27404step1Labels = raw27404step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27404step0 raw27404step0Labels permutation151 permutation2
    mixedMoment B raw27404step1 raw27404step1Labels = mixedMoment B raw27404step2 raw27404step2Labels := by
      have ha : raw27404step2 = -raw27404step1 := by apply Matrix.ext; change ∀ i j, raw27404step2 i j = -(raw27404step1 i j); unfold raw27404step2 raw27404step1; decide +kernel
      have hl : raw27404step2Labels = raw27404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

theorem canonical27405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27405 raw27405Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw27405 raw27405Labels = mixedMoment B raw27405step0 raw27405step0Labels := by
      have ha : raw27405step0 = (fun i j => raw27405 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27405step0 raw27405; decide +kernel
      have hl : raw27405step0Labels = raw27405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27405 raw27405Labels permutation682 permutation2
    mixedMoment B raw27405step0 raw27405step0Labels = mixedMoment B raw27405step1 raw27405step1Labels := by
      have ha : raw27405step1 = -raw27405step0 := by apply Matrix.ext; change ∀ i j, raw27405step1 i j = -(raw27405step0 i j); unfold raw27405step1 raw27405step0; decide +kernel
      have hl : raw27405step1Labels = raw27405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2423 node2423Labels := by rfl

theorem canonical27406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27406 raw27406Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw27406 raw27406Labels = mixedMoment B raw27406step0 raw27406step0Labels := by
      have hz : ∀ j, raw27406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27406step0 = (fun i j => raw27406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27406step0 raw27406; decide +kernel
      have hl : raw27406step0Labels = raw27406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27406 raw27406Labels permutation346 hz
    mixedMoment B raw27406step0 raw27406step0Labels = mixedMoment B raw27406step1 raw27406step1Labels := by
      have ha : raw27406step1 = (fun i j => raw27406step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27406step1 raw27406step0; decide +kernel
      have hl : raw27406step1Labels = raw27406step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27406step0 raw27406step0Labels permutation151 permutation2
    mixedMoment B raw27406step1 raw27406step1Labels = mixedMoment B raw27406step2 raw27406step2Labels := by
      have ha : raw27406step2 = -raw27406step1 := by apply Matrix.ext; change ∀ i j, raw27406step2 i j = -(raw27406step1 i j); unfold raw27406step2 raw27406step1; decide +kernel
      have hl : raw27406step2Labels = raw27406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2443 node2443Labels := by rfl

theorem canonical27407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27407 raw27407Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw27407 raw27407Labels = mixedMoment B raw27407step0 raw27407step0Labels := by
      have hz : ∀ j, raw27407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27407step0 = (fun i j => raw27407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27407step0 raw27407; decide +kernel
      have hl : raw27407step0Labels = raw27407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27407 raw27407Labels permutation346 hz
    mixedMoment B raw27407step0 raw27407step0Labels = mixedMoment B raw27407step1 raw27407step1Labels := by
      have ha : raw27407step1 = (fun i j => raw27407step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27407step1 raw27407step0; decide +kernel
      have hl : raw27407step1Labels = raw27407step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27407step0 raw27407step0Labels permutation151 permutation2
    mixedMoment B raw27407step1 raw27407step1Labels = mixedMoment B raw27407step2 raw27407step2Labels := by
      have ha : raw27407step2 = -raw27407step1 := by apply Matrix.ext; change ∀ i j, raw27407step2 i j = -(raw27407step1 i j); unfold raw27407step2 raw27407step1; decide +kernel
      have hl : raw27407step2Labels = raw27407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

theorem canonical27408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27408 raw27408Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw27408 raw27408Labels = mixedMoment B raw27408step0 raw27408step0Labels := by
      have hz : ∀ j, raw27408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27408step0 = (fun i j => raw27408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27408step0 raw27408; decide +kernel
      have hl : raw27408step0Labels = raw27408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27408 raw27408Labels permutation346 hz
    mixedMoment B raw27408step0 raw27408step0Labels = mixedMoment B raw27408step1 raw27408step1Labels := by
      have ha : raw27408step1 = (fun i j => raw27408step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27408step1 raw27408step0; decide +kernel
      have hl : raw27408step1Labels = raw27408step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27408step0 raw27408step0Labels permutation151 permutation2
    mixedMoment B raw27408step1 raw27408step1Labels = mixedMoment B raw27408step2 raw27408step2Labels := by
      have ha : raw27408step2 = -raw27408step1 := by apply Matrix.ext; change ∀ i j, raw27408step2 i j = -(raw27408step1 i j); unfold raw27408step2 raw27408step1; decide +kernel
      have hl : raw27408step2Labels = raw27408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1121 node1121Labels := by rfl

theorem canonical27409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27409 raw27409Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27409 raw27409Labels = mixedMoment B raw27409step0 raw27409step0Labels := by
      have hz : ∀ j, raw27409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27409step0 = (fun i j => raw27409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27409step0 raw27409; decide +kernel
      have hl : raw27409step0Labels = raw27409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27409 raw27409Labels permutation346 hz
    mixedMoment B raw27409step0 raw27409step0Labels = mixedMoment B raw27409step1 raw27409step1Labels := by
      have hz : ∀ j, raw27409step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27409step1 = (fun i j => raw27409step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27409step1 raw27409step0; decide +kernel
      have hl : raw27409step1Labels = raw27409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27409step0 raw27409step0Labels permutation32 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical27410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27410 raw27410Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw27410 raw27410Labels = mixedMoment B raw27410step0 raw27410step0Labels := by
      have ha : raw27410step0 = (fun i j => raw27410 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27410step0 raw27410; decide +kernel
      have hl : raw27410step0Labels = raw27410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27410 raw27410Labels permutation681 permutation2
    _ = mixedMoment B node3434 node3434Labels := by rfl

theorem canonical27411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27411 raw27411Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw27411 raw27411Labels = mixedMoment B raw27411step0 raw27411step0Labels := by
      have hz : ∀ j, raw27411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27411step0 = (fun i j => raw27411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27411step0 raw27411; decide +kernel
      have hl : raw27411step0Labels = raw27411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27411 raw27411Labels permutation434 hz
    mixedMoment B raw27411step0 raw27411step0Labels = mixedMoment B raw27411step1 raw27411step1Labels := by
      have hz : ∀ j, raw27411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27411step1 = (fun i j => raw27411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27411step1 raw27411step0; decide +kernel
      have hl : raw27411step1Labels = raw27411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27411step0 raw27411step0Labels permutation80 hz
    mixedMoment B raw27411step1 raw27411step1Labels = mixedMoment B raw27411step2 raw27411step2Labels := by
      have ha : raw27411step2 = (fun i j => raw27411step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27411step2 raw27411step1; decide +kernel
      have hl : raw27411step2Labels = raw27411step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27411step1 raw27411step1Labels permutation30 permutation2
    _ = mixedMoment B node3486 node3486Labels := by rfl

theorem canonical27412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27412 raw27412Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw27412 raw27412Labels = mixedMoment B raw27412step0 raw27412step0Labels := by
      have hz : ∀ j, raw27412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27412step0 = (fun i j => raw27412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27412step0 raw27412; decide +kernel
      have hl : raw27412step0Labels = raw27412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27412 raw27412Labels permutation346 hz
    mixedMoment B raw27412step0 raw27412step0Labels = mixedMoment B raw27412step1 raw27412step1Labels := by
      have ha : raw27412step1 = (fun i j => raw27412step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27412step1 raw27412step0; decide +kernel
      have hl : raw27412step1Labels = raw27412step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27412step0 raw27412step0Labels permutation150 permutation2
    _ = mixedMoment B node3355 node3355Labels := by rfl

theorem canonical27413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27413 raw27413Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw27413 raw27413Labels = mixedMoment B raw27413step0 raw27413step0Labels := by
      have hz : ∀ j, raw27413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27413step0 = (fun i j => raw27413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27413step0 raw27413; decide +kernel
      have hl : raw27413step0Labels = raw27413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27413 raw27413Labels permutation346 hz
    mixedMoment B raw27413step0 raw27413step0Labels = mixedMoment B raw27413step1 raw27413step1Labels := by
      have ha : raw27413step1 = (fun i j => raw27413step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27413step1 raw27413step0; decide +kernel
      have hl : raw27413step1Labels = raw27413step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27413step0 raw27413step0Labels permutation150 permutation2
    _ = mixedMoment B node1946 node1946Labels := by rfl

theorem canonical27414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27414 raw27414Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw27414 raw27414Labels = mixedMoment B raw27414step0 raw27414step0Labels := by
      have hz : ∀ j, raw27414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27414step0 = (fun i j => raw27414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27414step0 raw27414; decide +kernel
      have hl : raw27414step0Labels = raw27414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27414 raw27414Labels permutation434 hz
    mixedMoment B raw27414step0 raw27414step0Labels = mixedMoment B raw27414step1 raw27414step1Labels := by
      have hz : ∀ j, raw27414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27414step1 = (fun i j => raw27414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27414step1 raw27414step0; decide +kernel
      have hl : raw27414step1Labels = raw27414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27414step0 raw27414step0Labels permutation80 hz
    mixedMoment B raw27414step1 raw27414step1Labels = mixedMoment B raw27414step2 raw27414step2Labels := by
      have ha : raw27414step2 = (fun i j => raw27414step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27414step2 raw27414step1; decide +kernel
      have hl : raw27414step2Labels = raw27414step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27414step1 raw27414step1Labels permutation11 permutation4
    mixedMoment B raw27414step2 raw27414step2Labels = mixedMoment B raw27414step3 raw27414step3Labels := by
      have ha : raw27414step3 = -raw27414step2 := by apply Matrix.ext; change ∀ i j, raw27414step3 i j = -(raw27414step2 i j); unfold raw27414step3 raw27414step2; decide +kernel
      have hl : raw27414step3Labels = raw27414step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical27415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27415 raw27415Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27415 raw27415Labels = mixedMoment B raw27415step0 raw27415step0Labels := by
      have hz : ∀ j, raw27415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27415step0 = (fun i j => raw27415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27415step0 raw27415; decide +kernel
      have hl : raw27415step0Labels = raw27415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27415 raw27415Labels permutation434 hz
    mixedMoment B raw27415step0 raw27415step0Labels = mixedMoment B raw27415step1 raw27415step1Labels := by
      have ha : raw27415step1 = (fun i j => raw27415step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27415step1 raw27415step0; decide +kernel
      have hl : raw27415step1Labels = raw27415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27415step0 raw27415step0Labels permutation44 permutation4
    mixedMoment B raw27415step1 raw27415step1Labels = mixedMoment B raw27415step2 raw27415step2Labels := by
      have ha : raw27415step2 = -raw27415step1 := by apply Matrix.ext; change ∀ i j, raw27415step2 i j = -(raw27415step1 i j); unfold raw27415step2 raw27415step1; decide +kernel
      have hl : raw27415step2Labels = raw27415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27416 raw27416Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27416 raw27416Labels = mixedMoment B raw27416step0 raw27416step0Labels := by
      have hz : ∀ j, raw27416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27416step0 = (fun i j => raw27416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27416step0 raw27416; decide +kernel
      have hl : raw27416step0Labels = raw27416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27416 raw27416Labels permutation434 hz
    mixedMoment B raw27416step0 raw27416step0Labels = mixedMoment B raw27416step1 raw27416step1Labels := by
      have hz : ∀ j, raw27416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27416step1 = (fun i j => raw27416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27416step1 raw27416step0; decide +kernel
      have hl : raw27416step1Labels = raw27416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27416step0 raw27416step0Labels permutation80 hz
    mixedMoment B raw27416step1 raw27416step1Labels = mixedMoment B raw27416step2 raw27416step2Labels := by
      have ha : raw27416step2 = (fun i j => raw27416step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27416step2 raw27416step1; decide +kernel
      have hl : raw27416step2Labels = raw27416step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27416step1 raw27416step1Labels permutation8 permutation4
    mixedMoment B raw27416step2 raw27416step2Labels = mixedMoment B raw27416step3 raw27416step3Labels := by
      have ha : raw27416step3 = -raw27416step2 := by apply Matrix.ext; change ∀ i j, raw27416step3 i j = -(raw27416step2 i j); unfold raw27416step3 raw27416step2; decide +kernel
      have hl : raw27416step3Labels = raw27416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical27417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27417 raw27417Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw27417 raw27417Labels = mixedMoment B raw27417step0 raw27417step0Labels := by
      have hz : ∀ j, raw27417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27417step0 = (fun i j => raw27417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27417step0 raw27417; decide +kernel
      have hl : raw27417step0Labels = raw27417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27417 raw27417Labels permutation434 hz
    mixedMoment B raw27417step0 raw27417step0Labels = mixedMoment B raw27417step1 raw27417step1Labels := by
      have hz : ∀ j, raw27417step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27417step1 = (fun i j => raw27417step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27417step1 raw27417step0; decide +kernel
      have hl : raw27417step1Labels = raw27417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27417step0 raw27417step0Labels permutation80 hz
    mixedMoment B raw27417step1 raw27417step1Labels = mixedMoment B raw27417step2 raw27417step2Labels := by
      have ha : raw27417step2 = (fun i j => raw27417step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27417step2 raw27417step1; decide +kernel
      have hl : raw27417step2Labels = raw27417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27417step1 raw27417step1Labels permutation10 permutation4
    mixedMoment B raw27417step2 raw27417step2Labels = mixedMoment B raw27417step3 raw27417step3Labels := by
      have ha : raw27417step3 = -raw27417step2 := by apply Matrix.ext; change ∀ i j, raw27417step3 i j = -(raw27417step2 i j); unfold raw27417step3 raw27417step2; decide +kernel
      have hl : raw27417step3Labels = raw27417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical27418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27418 raw27418Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw27418 raw27418Labels = mixedMoment B raw27418step0 raw27418step0Labels := by
      have hz : ∀ j, raw27418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27418step0 = (fun i j => raw27418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27418step0 raw27418; decide +kernel
      have hl : raw27418step0Labels = raw27418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27418 raw27418Labels permutation346 hz
    mixedMoment B raw27418step0 raw27418step0Labels = mixedMoment B raw27418step1 raw27418step1Labels := by
      have ha : raw27418step1 = (fun i j => raw27418step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27418step1 raw27418step0; decide +kernel
      have hl : raw27418step1Labels = raw27418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27418step0 raw27418step0Labels permutation151 permutation2
    mixedMoment B raw27418step1 raw27418step1Labels = mixedMoment B raw27418step2 raw27418step2Labels := by
      have ha : raw27418step2 = -raw27418step1 := by apply Matrix.ext; change ∀ i j, raw27418step2 i j = -(raw27418step1 i j); unfold raw27418step2 raw27418step1; decide +kernel
      have hl : raw27418step2Labels = raw27418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

theorem canonical27419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27419 raw27419Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw27419 raw27419Labels = mixedMoment B raw27419step0 raw27419step0Labels := by
      have hz : ∀ j, raw27419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27419step0 = (fun i j => raw27419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27419step0 raw27419; decide +kernel
      have hl : raw27419step0Labels = raw27419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27419 raw27419Labels permutation346 hz
    mixedMoment B raw27419step0 raw27419step0Labels = mixedMoment B raw27419step1 raw27419step1Labels := by
      have ha : raw27419step1 = (fun i j => raw27419step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27419step1 raw27419step0; decide +kernel
      have hl : raw27419step1Labels = raw27419step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27419step0 raw27419step0Labels permutation150 permutation2
    mixedMoment B raw27419step1 raw27419step1Labels = mixedMoment B raw27419step2 raw27419step2Labels := by
      have ha : raw27419step2 = -raw27419step1 := by apply Matrix.ext; change ∀ i j, raw27419step2 i j = -(raw27419step1 i j); unfold raw27419step2 raw27419step1; decide +kernel
      have hl : raw27419step2Labels = raw27419step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical27420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27420 raw27420Labels = mixedMoment B node1923 node1923Labels := by
  calc
    mixedMoment B raw27420 raw27420Labels = mixedMoment B raw27420step0 raw27420step0Labels := by
      have ha : raw27420step0 = (fun i j => raw27420 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27420step0 raw27420; decide +kernel
      have hl : raw27420step0Labels = raw27420Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27420 raw27420Labels permutation688 permutation2
    mixedMoment B raw27420step0 raw27420step0Labels = mixedMoment B raw27420step1 raw27420step1Labels := by
      have ha : raw27420step1 = -raw27420step0 := by apply Matrix.ext; change ∀ i j, raw27420step1 i j = -(raw27420step0 i j); unfold raw27420step1 raw27420step0; decide +kernel
      have hl : raw27420step1Labels = raw27420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1923 node1923Labels := by rfl

theorem canonical27421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27421 raw27421Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw27421 raw27421Labels = mixedMoment B raw27421step0 raw27421step0Labels := by
      have hz : ∀ j, raw27421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27421step0 = (fun i j => raw27421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27421step0 raw27421; decide +kernel
      have hl : raw27421step0Labels = raw27421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27421 raw27421Labels permutation346 hz
    mixedMoment B raw27421step0 raw27421step0Labels = mixedMoment B raw27421step1 raw27421step1Labels := by
      have ha : raw27421step1 = (fun i j => raw27421step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27421step1 raw27421step0; decide +kernel
      have hl : raw27421step1Labels = raw27421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27421step0 raw27421step0Labels permutation149 permutation2
    mixedMoment B raw27421step1 raw27421step1Labels = mixedMoment B raw27421step2 raw27421step2Labels := by
      have ha : raw27421step2 = -raw27421step1 := by apply Matrix.ext; change ∀ i j, raw27421step2 i j = -(raw27421step1 i j); unfold raw27421step2 raw27421step1; decide +kernel
      have hl : raw27421step2Labels = raw27421step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1949 node1949Labels := by rfl

theorem canonical27422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27422 raw27422Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw27422 raw27422Labels = mixedMoment B raw27422step0 raw27422step0Labels := by
      have hz : ∀ j, raw27422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27422step0 = (fun i j => raw27422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27422step0 raw27422; decide +kernel
      have hl : raw27422step0Labels = raw27422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27422 raw27422Labels permutation346 hz
    mixedMoment B raw27422step0 raw27422step0Labels = mixedMoment B raw27422step1 raw27422step1Labels := by
      have ha : raw27422step1 = (fun i j => raw27422step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27422step1 raw27422step0; decide +kernel
      have hl : raw27422step1Labels = raw27422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27422step0 raw27422step0Labels permutation151 permutation2
    mixedMoment B raw27422step1 raw27422step1Labels = mixedMoment B raw27422step2 raw27422step2Labels := by
      have ha : raw27422step2 = -raw27422step1 := by apply Matrix.ext; change ∀ i j, raw27422step2 i j = -(raw27422step1 i j); unfold raw27422step2 raw27422step1; decide +kernel
      have hl : raw27422step2Labels = raw27422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical27423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27423 raw27423Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw27423 raw27423Labels = mixedMoment B raw27423step0 raw27423step0Labels := by
      have hz : ∀ j, raw27423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27423step0 = (fun i j => raw27423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27423step0 raw27423; decide +kernel
      have hl : raw27423step0Labels = raw27423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27423 raw27423Labels permutation346 hz
    mixedMoment B raw27423step0 raw27423step0Labels = mixedMoment B raw27423step1 raw27423step1Labels := by
      have ha : raw27423step1 = (fun i j => raw27423step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27423step1 raw27423step0; decide +kernel
      have hl : raw27423step1Labels = raw27423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27423step0 raw27423step0Labels permutation151 permutation2
    mixedMoment B raw27423step1 raw27423step1Labels = mixedMoment B raw27423step2 raw27423step2Labels := by
      have ha : raw27423step2 = -raw27423step1 := by apply Matrix.ext; change ∀ i j, raw27423step2 i j = -(raw27423step1 i j); unfold raw27423step2 raw27423step1; decide +kernel
      have hl : raw27423step2Labels = raw27423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical27424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27424 raw27424Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27424 raw27424Labels = mixedMoment B raw27424step0 raw27424step0Labels := by
      have hz : ∀ j, raw27424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27424step0 = (fun i j => raw27424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27424step0 raw27424; decide +kernel
      have hl : raw27424step0Labels = raw27424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27424 raw27424Labels permutation346 hz
    mixedMoment B raw27424step0 raw27424step0Labels = mixedMoment B raw27424step1 raw27424step1Labels := by
      have hz : ∀ j, raw27424step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27424step1 = (fun i j => raw27424step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27424step1 raw27424step0; decide +kernel
      have hl : raw27424step1Labels = raw27424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27424step0 raw27424step0Labels permutation32 hz
    mixedMoment B raw27424step1 raw27424step1Labels = mixedMoment B raw27424step2 raw27424step2Labels := by
      have ha : raw27424step2 = (fun i j => raw27424step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27424step2 raw27424step1; decide +kernel
      have hl : raw27424step2Labels = raw27424step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27424step1 raw27424step1Labels permutation30 permutation0
    mixedMoment B raw27424step2 raw27424step2Labels = mixedMoment B raw27424step3 raw27424step3Labels := by
      have ha : raw27424step3 = -raw27424step2 := by apply Matrix.ext; change ∀ i j, raw27424step3 i j = -(raw27424step2 i j); unfold raw27424step3 raw27424step2; decide +kernel
      have hl : raw27424step3Labels = raw27424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical27425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27425 raw27425Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw27425 raw27425Labels = mixedMoment B raw27425step0 raw27425step0Labels := by
      have hz : ∀ j, raw27425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27425step0 = (fun i j => raw27425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27425step0 raw27425; decide +kernel
      have hl : raw27425step0Labels = raw27425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27425 raw27425Labels permutation434 hz
    mixedMoment B raw27425step0 raw27425step0Labels = mixedMoment B raw27425step1 raw27425step1Labels := by
      have hz : ∀ j, raw27425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27425step1 = (fun i j => raw27425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27425step1 raw27425step0; decide +kernel
      have hl : raw27425step1Labels = raw27425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27425step0 raw27425step0Labels permutation80 hz
    mixedMoment B raw27425step1 raw27425step1Labels = mixedMoment B raw27425step2 raw27425step2Labels := by
      have ha : raw27425step2 = (fun i j => raw27425step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27425step2 raw27425step1; decide +kernel
      have hl : raw27425step2Labels = raw27425step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27425step1 raw27425step1Labels permutation30 permutation2
    mixedMoment B raw27425step2 raw27425step2Labels = mixedMoment B raw27425step3 raw27425step3Labels := by
      have ha : raw27425step3 = -raw27425step2 := by apply Matrix.ext; change ∀ i j, raw27425step3 i j = -(raw27425step2 i j); unfold raw27425step3 raw27425step2; decide +kernel
      have hl : raw27425step3Labels = raw27425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical27426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27426 raw27426Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw27426 raw27426Labels = mixedMoment B raw27426step0 raw27426step0Labels := by
      have hz : ∀ j, raw27426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27426step0 = (fun i j => raw27426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27426step0 raw27426; decide +kernel
      have hl : raw27426step0Labels = raw27426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27426 raw27426Labels permutation434 hz
    mixedMoment B raw27426step0 raw27426step0Labels = mixedMoment B raw27426step1 raw27426step1Labels := by
      have hz : ∀ j, raw27426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27426step1 = (fun i j => raw27426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27426step1 raw27426step0; decide +kernel
      have hl : raw27426step1Labels = raw27426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27426step0 raw27426step0Labels permutation80 hz
    mixedMoment B raw27426step1 raw27426step1Labels = mixedMoment B raw27426step2 raw27426step2Labels := by
      have ha : raw27426step2 = (fun i j => raw27426step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27426step2 raw27426step1; decide +kernel
      have hl : raw27426step2Labels = raw27426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27426step1 raw27426step1Labels permutation31 permutation2
    mixedMoment B raw27426step2 raw27426step2Labels = mixedMoment B raw27426step3 raw27426step3Labels := by
      have ha : raw27426step3 = -raw27426step2 := by apply Matrix.ext; change ∀ i j, raw27426step3 i j = -(raw27426step2 i j); unfold raw27426step3 raw27426step2; decide +kernel
      have hl : raw27426step3Labels = raw27426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical27427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27427 raw27427Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw27427 raw27427Labels = mixedMoment B raw27427step0 raw27427step0Labels := by
      have hz : ∀ j, raw27427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27427step0 = (fun i j => raw27427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27427step0 raw27427; decide +kernel
      have hl : raw27427step0Labels = raw27427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27427 raw27427Labels permutation434 hz
    mixedMoment B raw27427step0 raw27427step0Labels = mixedMoment B raw27427step1 raw27427step1Labels := by
      have ha : raw27427step1 = (fun i j => raw27427step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27427step1 raw27427step0; decide +kernel
      have hl : raw27427step1Labels = raw27427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27427step0 raw27427step0Labels permutation151 permutation2
    mixedMoment B raw27427step1 raw27427step1Labels = mixedMoment B raw27427step2 raw27427step2Labels := by
      have ha : raw27427step2 = -raw27427step1 := by apply Matrix.ext; change ∀ i j, raw27427step2 i j = -(raw27427step1 i j); unfold raw27427step2 raw27427step1; decide +kernel
      have hl : raw27427step2Labels = raw27427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

theorem canonical27428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27428 raw27428Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw27428 raw27428Labels = mixedMoment B raw27428step0 raw27428step0Labels := by
      have hz : ∀ j, raw27428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27428step0 = (fun i j => raw27428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27428step0 raw27428; decide +kernel
      have hl : raw27428step0Labels = raw27428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27428 raw27428Labels permutation346 hz
    mixedMoment B raw27428step0 raw27428step0Labels = mixedMoment B raw27428step1 raw27428step1Labels := by
      have ha : raw27428step1 = (fun i j => raw27428step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27428step1 raw27428step0; decide +kernel
      have hl : raw27428step1Labels = raw27428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27428step0 raw27428step0Labels permutation151 permutation2
    mixedMoment B raw27428step1 raw27428step1Labels = mixedMoment B raw27428step2 raw27428step2Labels := by
      have ha : raw27428step2 = -raw27428step1 := by apply Matrix.ext; change ∀ i j, raw27428step2 i j = -(raw27428step1 i j); unfold raw27428step2 raw27428step1; decide +kernel
      have hl : raw27428step2Labels = raw27428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

theorem canonical27429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27429 raw27429Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw27429 raw27429Labels = mixedMoment B raw27429step0 raw27429step0Labels := by
      have hz : ∀ j, raw27429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27429step0 = (fun i j => raw27429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27429step0 raw27429; decide +kernel
      have hl : raw27429step0Labels = raw27429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27429 raw27429Labels permutation434 hz
    mixedMoment B raw27429step0 raw27429step0Labels = mixedMoment B raw27429step1 raw27429step1Labels := by
      have hz : ∀ j, raw27429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27429step1 = (fun i j => raw27429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27429step1 raw27429step0; decide +kernel
      have hl : raw27429step1Labels = raw27429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27429step0 raw27429step0Labels permutation80 hz
    mixedMoment B raw27429step1 raw27429step1Labels = mixedMoment B raw27429step2 raw27429step2Labels := by
      have ha : raw27429step2 = (fun i j => raw27429step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27429step2 raw27429step1; decide +kernel
      have hl : raw27429step2Labels = raw27429step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27429step1 raw27429step1Labels permutation31 permutation2
    mixedMoment B raw27429step2 raw27429step2Labels = mixedMoment B raw27429step3 raw27429step3Labels := by
      have ha : raw27429step3 = -raw27429step2 := by apply Matrix.ext; change ∀ i j, raw27429step3 i j = -(raw27429step2 i j); unfold raw27429step3 raw27429step2; decide +kernel
      have hl : raw27429step3Labels = raw27429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

theorem canonical27430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27430 raw27430Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw27430 raw27430Labels = mixedMoment B raw27430step0 raw27430step0Labels := by
      have hz : ∀ j, raw27430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27430step0 = (fun i j => raw27430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27430step0 raw27430; decide +kernel
      have hl : raw27430step0Labels = raw27430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27430 raw27430Labels permutation434 hz
    mixedMoment B raw27430step0 raw27430step0Labels = mixedMoment B raw27430step1 raw27430step1Labels := by
      have hz : ∀ j, raw27430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27430step1 = (fun i j => raw27430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27430step1 raw27430step0; decide +kernel
      have hl : raw27430step1Labels = raw27430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27430step0 raw27430step0Labels permutation80 hz
    mixedMoment B raw27430step1 raw27430step1Labels = mixedMoment B raw27430step2 raw27430step2Labels := by
      have ha : raw27430step2 = (fun i j => raw27430step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27430step2 raw27430step1; decide +kernel
      have hl : raw27430step2Labels = raw27430step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27430step1 raw27430step1Labels permutation31 permutation2
    mixedMoment B raw27430step2 raw27430step2Labels = mixedMoment B raw27430step3 raw27430step3Labels := by
      have ha : raw27430step3 = -raw27430step2 := by apply Matrix.ext; change ∀ i j, raw27430step3 i j = -(raw27430step2 i j); unfold raw27430step3 raw27430step2; decide +kernel
      have hl : raw27430step3Labels = raw27430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1146 node1146Labels := by rfl

theorem canonical27431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27431 raw27431Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw27431 raw27431Labels = mixedMoment B raw27431step0 raw27431step0Labels := by
      have hz : ∀ j, raw27431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27431step0 = (fun i j => raw27431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27431step0 raw27431; decide +kernel
      have hl : raw27431step0Labels = raw27431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431 raw27431Labels permutation434 hz
    mixedMoment B raw27431step0 raw27431step0Labels = mixedMoment B raw27431step1 raw27431step1Labels := by
      have hz : ∀ j, raw27431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27431step1 = (fun i j => raw27431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27431step1 raw27431step0; decide +kernel
      have hl : raw27431step1Labels = raw27431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431step0 raw27431step0Labels permutation80 hz
    mixedMoment B raw27431step1 raw27431step1Labels = mixedMoment B raw27431step2 raw27431step2Labels := by
      have hz : ∀ j, raw27431step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw27431step2 = (fun i j => raw27431step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw27431step2 raw27431step1; decide +kernel
      have hl : raw27431step2Labels = raw27431step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431step1 raw27431step1Labels permutation8 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical27432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27432 raw27432Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw27432 raw27432Labels = mixedMoment B raw27432step0 raw27432step0Labels := by
      have hz : ∀ j, raw27432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27432step0 = (fun i j => raw27432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27432step0 raw27432; decide +kernel
      have hl : raw27432step0Labels = raw27432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27432 raw27432Labels permutation434 hz
    mixedMoment B raw27432step0 raw27432step0Labels = mixedMoment B raw27432step1 raw27432step1Labels := by
      have ha : raw27432step1 = (fun i j => raw27432step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27432step1 raw27432step0; decide +kernel
      have hl : raw27432step1Labels = raw27432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27432step0 raw27432step0Labels permutation56 permutation2
    mixedMoment B raw27432step1 raw27432step1Labels = mixedMoment B raw27432step2 raw27432step2Labels := by
      have ha : raw27432step2 = -raw27432step1 := by apply Matrix.ext; change ∀ i j, raw27432step2 i j = -(raw27432step1 i j); unfold raw27432step2 raw27432step1; decide +kernel
      have hl : raw27432step2Labels = raw27432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2837 node2837Labels := by rfl

theorem canonical27433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27433 raw27433Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw27433 raw27433Labels = mixedMoment B raw27433step0 raw27433step0Labels := by
      have hz : ∀ j, raw27433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27433step0 = (fun i j => raw27433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27433step0 raw27433; decide +kernel
      have hl : raw27433step0Labels = raw27433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27433 raw27433Labels permutation346 hz
    mixedMoment B raw27433step0 raw27433step0Labels = mixedMoment B raw27433step1 raw27433step1Labels := by
      have ha : raw27433step1 = (fun i j => raw27433step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27433step1 raw27433step0; decide +kernel
      have hl : raw27433step1Labels = raw27433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27433step0 raw27433step0Labels permutation56 permutation2
    mixedMoment B raw27433step1 raw27433step1Labels = mixedMoment B raw27433step2 raw27433step2Labels := by
      have ha : raw27433step2 = -raw27433step1 := by apply Matrix.ext; change ∀ i j, raw27433step2 i j = -(raw27433step1 i j); unfold raw27433step2 raw27433step1; decide +kernel
      have hl : raw27433step2Labels = raw27433step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2837 node2837Labels := by rfl

theorem canonical27434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27434 raw27434Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw27434 raw27434Labels = mixedMoment B raw27434step0 raw27434step0Labels := by
      have hz : ∀ j, raw27434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27434step0 = (fun i j => raw27434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27434step0 raw27434; decide +kernel
      have hl : raw27434step0Labels = raw27434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27434 raw27434Labels permutation434 hz
    mixedMoment B raw27434step0 raw27434step0Labels = mixedMoment B raw27434step1 raw27434step1Labels := by
      have hz : ∀ j, raw27434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27434step1 = (fun i j => raw27434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27434step1 raw27434step0; decide +kernel
      have hl : raw27434step1Labels = raw27434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27434step0 raw27434step0Labels permutation80 hz
    mixedMoment B raw27434step1 raw27434step1Labels = mixedMoment B raw27434step2 raw27434step2Labels := by
      have ha : raw27434step2 = (fun i j => raw27434step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27434step2 raw27434step1; decide +kernel
      have hl : raw27434step2Labels = raw27434step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27434step1 raw27434step1Labels permutation14 permutation2
    mixedMoment B raw27434step2 raw27434step2Labels = mixedMoment B raw27434step3 raw27434step3Labels := by
      have ha : raw27434step3 = -raw27434step2 := by apply Matrix.ext; change ∀ i j, raw27434step3 i j = -(raw27434step2 i j); unfold raw27434step3 raw27434step2; decide +kernel
      have hl : raw27434step3Labels = raw27434step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2842 node2842Labels := by rfl

theorem canonical27435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27435 raw27435Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw27435 raw27435Labels = mixedMoment B raw27435step0 raw27435step0Labels := by
      have hz : ∀ j, raw27435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27435step0 = (fun i j => raw27435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27435step0 raw27435; decide +kernel
      have hl : raw27435step0Labels = raw27435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27435 raw27435Labels permutation434 hz
    mixedMoment B raw27435step0 raw27435step0Labels = mixedMoment B raw27435step1 raw27435step1Labels := by
      have hz : ∀ j, raw27435step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27435step1 = (fun i j => raw27435step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27435step1 raw27435step0; decide +kernel
      have hl : raw27435step1Labels = raw27435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27435step0 raw27435step0Labels permutation80 hz
    mixedMoment B raw27435step1 raw27435step1Labels = mixedMoment B raw27435step2 raw27435step2Labels := by
      have ha : raw27435step2 = (fun i j => raw27435step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27435step2 raw27435step1; decide +kernel
      have hl : raw27435step2Labels = raw27435step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27435step1 raw27435step1Labels permutation30 permutation2
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical27436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27436 raw27436Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw27436 raw27436Labels = mixedMoment B raw27436step0 raw27436step0Labels := by
      have hz : ∀ j, raw27436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27436step0 = (fun i j => raw27436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27436step0 raw27436; decide +kernel
      have hl : raw27436step0Labels = raw27436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27436 raw27436Labels permutation346 hz
    mixedMoment B raw27436step0 raw27436step0Labels = mixedMoment B raw27436step1 raw27436step1Labels := by
      have ha : raw27436step1 = (fun i j => raw27436step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27436step1 raw27436step0; decide +kernel
      have hl : raw27436step1Labels = raw27436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27436step0 raw27436step0Labels permutation34 permutation2
    _ = mixedMoment B node1132 node1132Labels := by rfl

theorem canonical27437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27437 raw27437Labels = mixedMoment B node2335 node2335Labels := by
  calc
    mixedMoment B raw27437 raw27437Labels = mixedMoment B raw27437step0 raw27437step0Labels := by
      have hz : ∀ j, raw27437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27437step0 = (fun i j => raw27437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27437step0 raw27437; decide +kernel
      have hl : raw27437step0Labels = raw27437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27437 raw27437Labels permutation346 hz
    mixedMoment B raw27437step0 raw27437step0Labels = mixedMoment B raw27437step1 raw27437step1Labels := by
      have ha : raw27437step1 = (fun i j => raw27437step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27437step1 raw27437step0; decide +kernel
      have hl : raw27437step1Labels = raw27437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27437step0 raw27437step0Labels permutation34 permutation2
    _ = mixedMoment B node2335 node2335Labels := by rfl

theorem canonical27438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27438 raw27438Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27438 raw27438Labels = mixedMoment B raw27438step0 raw27438step0Labels := by
      have ha : raw27438step0 = (fun i j => raw27438 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27438step0 raw27438; decide +kernel
      have hl : raw27438step0Labels = raw27438Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27438 raw27438Labels permutation154 permutation2
    _ = mixedMoment B node2426 node2426Labels := by rfl

theorem canonical27439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27439 raw27439Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw27439 raw27439Labels = mixedMoment B raw27439step0 raw27439step0Labels := by
      have hz : ∀ j, raw27439 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27439step0 = (fun i j => raw27439 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27439step0 raw27439; decide +kernel
      have hl : raw27439step0Labels = raw27439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27439 raw27439Labels permutation520 hz
    mixedMoment B raw27439step0 raw27439step0Labels = mixedMoment B raw27439step1 raw27439step1Labels := by
      have hz : ∀ j, raw27439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27439step1 = (fun i j => raw27439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27439step1 raw27439step0; decide +kernel
      have hl : raw27439step1Labels = raw27439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27439step0 raw27439step0Labels permutation80 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical27440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27440 raw27440Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw27440 raw27440Labels = mixedMoment B raw27440step0 raw27440step0Labels := by
      have hz : ∀ j, raw27440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27440step0 = (fun i j => raw27440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27440step0 raw27440; decide +kernel
      have hl : raw27440step0Labels = raw27440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27440 raw27440Labels permutation346 hz
    mixedMoment B raw27440step0 raw27440step0Labels = mixedMoment B raw27440step1 raw27440step1Labels := by
      have ha : raw27440step1 = (fun i j => raw27440step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27440step1 raw27440step0; decide +kernel
      have hl : raw27440step1Labels = raw27440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27440step0 raw27440step0Labels permutation38 permutation2
    mixedMoment B raw27440step1 raw27440step1Labels = mixedMoment B raw27440step2 raw27440step2Labels := by
      have ha : raw27440step2 = -raw27440step1 := by apply Matrix.ext; change ∀ i j, raw27440step2 i j = -(raw27440step1 i j); unfold raw27440step2 raw27440step1; decide +kernel
      have hl : raw27440step2Labels = raw27440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3385 node3385Labels := by rfl

theorem canonical27441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27441 raw27441Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw27441 raw27441Labels = mixedMoment B raw27441step0 raw27441step0Labels := by
      have ha : raw27441step0 = (fun i j => raw27441 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27441step0 raw27441; decide +kernel
      have hl : raw27441step0Labels = raw27441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27441 raw27441Labels permutation200 permutation2
    mixedMoment B raw27441step0 raw27441step0Labels = mixedMoment B raw27441step1 raw27441step1Labels := by
      have ha : raw27441step1 = -raw27441step0 := by apply Matrix.ext; change ∀ i j, raw27441step1 i j = -(raw27441step0 i j); unfold raw27441step1 raw27441step0; decide +kernel
      have hl : raw27441step1Labels = raw27441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3368 node3368Labels := by rfl

theorem canonical27442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27442 raw27442Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27442 raw27442Labels = mixedMoment B raw27442step0 raw27442step0Labels := by
      have hz : ∀ j, raw27442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27442step0 = (fun i j => raw27442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27442step0 raw27442; decide +kernel
      have hl : raw27442step0Labels = raw27442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27442 raw27442Labels permutation346 hz
    mixedMoment B raw27442step0 raw27442step0Labels = mixedMoment B raw27442step1 raw27442step1Labels := by
      have ha : raw27442step1 = (fun i j => raw27442step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27442step1 raw27442step0; decide +kernel
      have hl : raw27442step1Labels = raw27442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27442step0 raw27442step0Labels permutation149 permutation2
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27443 raw27443Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw27443 raw27443Labels = mixedMoment B raw27443step0 raw27443step0Labels := by
      have hz : ∀ j, raw27443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27443step0 = (fun i j => raw27443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27443step0 raw27443; decide +kernel
      have hl : raw27443step0Labels = raw27443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27443 raw27443Labels permutation346 hz
    mixedMoment B raw27443step0 raw27443step0Labels = mixedMoment B raw27443step1 raw27443step1Labels := by
      have ha : raw27443step1 = (fun i j => raw27443step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27443step1 raw27443step0; decide +kernel
      have hl : raw27443step1Labels = raw27443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27443step0 raw27443step0Labels permutation149 permutation2
    _ = mixedMoment B node3343 node3343Labels := by rfl

theorem canonical27444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27444 raw27444Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw27444 raw27444Labels = mixedMoment B raw27444step0 raw27444step0Labels := by
      have hz : ∀ j, raw27444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27444step0 = (fun i j => raw27444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27444step0 raw27444; decide +kernel
      have hl : raw27444step0Labels = raw27444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27444 raw27444Labels permutation346 hz
    mixedMoment B raw27444step0 raw27444step0Labels = mixedMoment B raw27444step1 raw27444step1Labels := by
      have ha : raw27444step1 = (fun i j => raw27444step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27444step1 raw27444step0; decide +kernel
      have hl : raw27444step1Labels = raw27444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27444step0 raw27444step0Labels permutation149 permutation2
    _ = mixedMoment B node1917 node1917Labels := by rfl

theorem canonical27445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27445 raw27445Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27445 raw27445Labels = mixedMoment B raw27445step0 raw27445step0Labels := by
      have hz : ∀ j, raw27445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27445step0 = (fun i j => raw27445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27445step0 raw27445; decide +kernel
      have hl : raw27445step0Labels = raw27445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27445 raw27445Labels permutation346 hz
    mixedMoment B raw27445step0 raw27445step0Labels = mixedMoment B raw27445step1 raw27445step1Labels := by
      have ha : raw27445step1 = (fun i j => raw27445step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27445step1 raw27445step0; decide +kernel
      have hl : raw27445step1Labels = raw27445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27445step0 raw27445step0Labels permutation32 permutation4
    mixedMoment B raw27445step1 raw27445step1Labels = mixedMoment B raw27445step2 raw27445step2Labels := by
      have ha : raw27445step2 = -raw27445step1 := by apply Matrix.ext; change ∀ i j, raw27445step2 i j = -(raw27445step1 i j); unfold raw27445step2 raw27445step1; decide +kernel
      have hl : raw27445step2Labels = raw27445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27446 raw27446Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27446 raw27446Labels = mixedMoment B raw27446step0 raw27446step0Labels := by
      have hz : ∀ j, raw27446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27446step0 = (fun i j => raw27446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27446step0 raw27446; decide +kernel
      have hl : raw27446step0Labels = raw27446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27446 raw27446Labels permutation346 hz
    mixedMoment B raw27446step0 raw27446step0Labels = mixedMoment B raw27446step1 raw27446step1Labels := by
      have ha : raw27446step1 = (fun i j => raw27446step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27446step1 raw27446step0; decide +kernel
      have hl : raw27446step1Labels = raw27446step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27446step0 raw27446step0Labels permutation34 permutation4
    mixedMoment B raw27446step1 raw27446step1Labels = mixedMoment B raw27446step2 raw27446step2Labels := by
      have ha : raw27446step2 = -raw27446step1 := by apply Matrix.ext; change ∀ i j, raw27446step2 i j = -(raw27446step1 i j); unfold raw27446step2 raw27446step1; decide +kernel
      have hl : raw27446step2Labels = raw27446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27447 raw27447Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw27447 raw27447Labels = mixedMoment B raw27447step0 raw27447step0Labels := by
      have ha : raw27447step0 = (fun i j => raw27447 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27447step0 raw27447; decide +kernel
      have hl : raw27447step0Labels = raw27447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27447 raw27447Labels permutation160 permutation2
    _ = mixedMoment B node1112 node1112Labels := by rfl

theorem canonical27448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27448 raw27448Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw27448 raw27448Labels = mixedMoment B raw27448step0 raw27448step0Labels := by
      have ha : raw27448step0 = (fun i j => raw27448 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27448step0 raw27448; decide +kernel
      have hl : raw27448step0Labels = raw27448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27448 raw27448Labels permutation160 permutation2
    _ = mixedMoment B node2320 node2320Labels := by rfl

theorem canonical27449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27449 raw27449Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw27449 raw27449Labels = mixedMoment B raw27449step0 raw27449step0Labels := by
      have ha : raw27449step0 = (fun i j => raw27449 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27449step0 raw27449; decide +kernel
      have hl : raw27449step0Labels = raw27449Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27449 raw27449Labels permutation160 permutation2
    _ = mixedMoment B node2437 node2437Labels := by rfl

theorem canonical27450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27450 raw27450Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27450 raw27450Labels = mixedMoment B raw27450step0 raw27450step0Labels := by
      have hz : ∀ j, raw27450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27450step0 = (fun i j => raw27450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27450step0 raw27450; decide +kernel
      have hl : raw27450step0Labels = raw27450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27450 raw27450Labels permutation520 hz
    mixedMoment B raw27450step0 raw27450step0Labels = mixedMoment B raw27450step1 raw27450step1Labels := by
      have ha : raw27450step1 = (fun i j => raw27450step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27450step1 raw27450step0; decide +kernel
      have hl : raw27450step1Labels = raw27450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27450step0 raw27450step0Labels permutation34 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical27451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27451 raw27451Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw27451 raw27451Labels = mixedMoment B raw27451step0 raw27451step0Labels := by
      have ha : raw27451step0 = (fun i j => raw27451 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27451step0 raw27451; decide +kernel
      have hl : raw27451step0Labels = raw27451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27451 raw27451Labels permutation674 permutation2
    _ = mixedMoment B node3443 node3443Labels := by rfl

theorem canonical27452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27452 raw27452Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27452 raw27452Labels = mixedMoment B raw27452step0 raw27452step0Labels := by
      have hz : ∀ j, raw27452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27452step0 = (fun i j => raw27452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27452step0 raw27452; decide +kernel
      have hl : raw27452step0Labels = raw27452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27452 raw27452Labels permutation434 hz
    mixedMoment B raw27452step0 raw27452step0Labels = mixedMoment B raw27452step1 raw27452step1Labels := by
      have ha : raw27452step1 = (fun i j => raw27452step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27452step1 raw27452step0; decide +kernel
      have hl : raw27452step1Labels = raw27452step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27452step0 raw27452step0Labels permutation149 permutation2
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27453 raw27453Labels = mixedMoment B node3339 node3339Labels := by
  calc
    mixedMoment B raw27453 raw27453Labels = mixedMoment B raw27453step0 raw27453step0Labels := by
      have ha : raw27453step0 = (fun i j => raw27453 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27453step0 raw27453; decide +kernel
      have hl : raw27453step0Labels = raw27453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27453 raw27453Labels permutation674 permutation2
    _ = mixedMoment B node3339 node3339Labels := by rfl

theorem canonical27454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27454 raw27454Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw27454 raw27454Labels = mixedMoment B raw27454step0 raw27454step0Labels := by
      have ha : raw27454step0 = (fun i j => raw27454 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27454step0 raw27454; decide +kernel
      have hl : raw27454step0Labels = raw27454Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27454 raw27454Labels permutation674 permutation2
    _ = mixedMoment B node1907 node1907Labels := by rfl

theorem canonical27460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27460 raw27460Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw27460 raw27460Labels = mixedMoment B raw27460step0 raw27460step0Labels := by
      have hz : ∀ j, raw27460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27460step0 = (fun i j => raw27460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27460step0 raw27460; decide +kernel
      have hl : raw27460step0Labels = raw27460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27460 raw27460Labels permutation434 hz
    mixedMoment B raw27460step0 raw27460step0Labels = mixedMoment B raw27460step1 raw27460step1Labels := by
      have ha : raw27460step1 = (fun i j => raw27460step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27460step1 raw27460step0; decide +kernel
      have hl : raw27460step1Labels = raw27460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27460step0 raw27460step0Labels permutation149 permutation2
    mixedMoment B raw27460step1 raw27460step1Labels = mixedMoment B raw27460step2 raw27460step2Labels := by
      have ha : raw27460step2 = -raw27460step1 := by apply Matrix.ext; change ∀ i j, raw27460step2 i j = -(raw27460step1 i j); unfold raw27460step2 raw27460step1; decide +kernel
      have hl : raw27460step2Labels = raw27460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical27461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27461 raw27461Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw27461 raw27461Labels = mixedMoment B raw27461step0 raw27461step0Labels := by
      have hz : ∀ j, raw27461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27461step0 = (fun i j => raw27461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27461step0 raw27461; decide +kernel
      have hl : raw27461step0Labels = raw27461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27461 raw27461Labels permutation434 hz
    mixedMoment B raw27461step0 raw27461step0Labels = mixedMoment B raw27461step1 raw27461step1Labels := by
      have hz : ∀ j, raw27461step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27461step1 = (fun i j => raw27461step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27461step1 raw27461step0; decide +kernel
      have hl : raw27461step1Labels = raw27461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27461step0 raw27461step0Labels permutation56 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical27462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27462 raw27462Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw27462 raw27462Labels = mixedMoment B raw27462step0 raw27462step0Labels := by
      have hz : ∀ j, raw27462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27462step0 = (fun i j => raw27462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27462step0 raw27462; decide +kernel
      have hl : raw27462step0Labels = raw27462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27462 raw27462Labels permutation434 hz
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical27463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27463 raw27463Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27463 raw27463Labels = mixedMoment B raw27463step0 raw27463step0Labels := by
      have ha : raw27463step0 = (fun i j => raw27463 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27463step0 raw27463; decide +kernel
      have hl : raw27463step0Labels = raw27463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27463 raw27463Labels permutation176 permutation2
    _ = mixedMoment B node2426 node2426Labels := by rfl

theorem canonical27464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27464 raw27464Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw27464 raw27464Labels = mixedMoment B raw27464step0 raw27464step0Labels := by
      have hz : ∀ j, raw27464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27464step0 = (fun i j => raw27464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27464step0 raw27464; decide +kernel
      have hl : raw27464step0Labels = raw27464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27464 raw27464Labels permutation434 hz
    mixedMoment B raw27464step0 raw27464step0Labels = mixedMoment B raw27464step1 raw27464step1Labels := by
      have ha : raw27464step1 = (fun i j => raw27464step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27464step1 raw27464step0; decide +kernel
      have hl : raw27464step1Labels = raw27464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27464step0 raw27464step0Labels permutation38 permutation2
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical27465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27465 raw27465Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw27465 raw27465Labels = mixedMoment B raw27465step0 raw27465step0Labels := by
      have hz : ∀ j, raw27465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27465step0 = (fun i j => raw27465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27465step0 raw27465; decide +kernel
      have hl : raw27465step0Labels = raw27465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27465 raw27465Labels permutation434 hz
    mixedMoment B raw27465step0 raw27465step0Labels = mixedMoment B raw27465step1 raw27465step1Labels := by
      have ha : raw27465step1 = (fun i j => raw27465step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27465step1 raw27465step0; decide +kernel
      have hl : raw27465step1Labels = raw27465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27465step0 raw27465step0Labels permutation149 permutation2
    mixedMoment B raw27465step1 raw27465step1Labels = mixedMoment B raw27465step2 raw27465step2Labels := by
      have ha : raw27465step2 = -raw27465step1 := by apply Matrix.ext; change ∀ i j, raw27465step2 i j = -(raw27465step1 i j); unfold raw27465step2 raw27465step1; decide +kernel
      have hl : raw27465step2Labels = raw27465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1317 node1317Labels := by rfl

theorem canonical27466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27466 raw27466Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27466 raw27466Labels = mixedMoment B raw27466step0 raw27466step0Labels := by
      have hz : ∀ j, raw27466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27466step0 = (fun i j => raw27466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27466step0 raw27466; decide +kernel
      have hl : raw27466step0Labels = raw27466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466 raw27466Labels permutation434 hz
    mixedMoment B raw27466step0 raw27466step0Labels = mixedMoment B raw27466step1 raw27466step1Labels := by
      have hz : ∀ j, raw27466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27466step1 = (fun i j => raw27466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27466step1 raw27466step0; decide +kernel
      have hl : raw27466step1Labels = raw27466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466step0 raw27466step0Labels permutation56 hz
    mixedMoment B raw27466step1 raw27466step1Labels = mixedMoment B raw27466step2 raw27466step2Labels := by
      have ha : raw27466step2 = (fun i j => raw27466step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27466step2 raw27466step1; decide +kernel
      have hl : raw27466step2Labels = raw27466step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27466step1 raw27466step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical27467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27467 raw27467Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw27467 raw27467Labels = mixedMoment B raw27467step0 raw27467step0Labels := by
      have hz : ∀ j, raw27467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27467step0 = (fun i j => raw27467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27467step0 raw27467; decide +kernel
      have hl : raw27467step0Labels = raw27467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27467 raw27467Labels permutation434 hz
    _ = mixedMoment B node1155 node1155Labels := by rfl

theorem canonical27468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27468 raw27468Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw27468 raw27468Labels = mixedMoment B raw27468step0 raw27468step0Labels := by
      have hz : ∀ j, raw27468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27468step0 = (fun i j => raw27468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27468step0 raw27468; decide +kernel
      have hl : raw27468step0Labels = raw27468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27468 raw27468Labels permutation434 hz
    _ = mixedMoment B node2352 node2352Labels := by rfl

theorem canonical27469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27469 raw27469Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw27469 raw27469Labels = mixedMoment B raw27469step0 raw27469step0Labels := by
      have ha : raw27469step0 = (fun i j => raw27469 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27469step0 raw27469; decide +kernel
      have hl : raw27469step0Labels = raw27469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27469 raw27469Labels permutation158 permutation2
    _ = mixedMoment B node2524 node2524Labels := by rfl

theorem canonical27470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27470 raw27470Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw27470 raw27470Labels = mixedMoment B raw27470step0 raw27470step0Labels := by
      have hz : ∀ j, raw27470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27470step0 = (fun i j => raw27470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27470step0 raw27470; decide +kernel
      have hl : raw27470step0Labels = raw27470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27470 raw27470Labels permutation434 hz
    mixedMoment B raw27470step0 raw27470step0Labels = mixedMoment B raw27470step1 raw27470step1Labels := by
      have ha : raw27470step1 = (fun i j => raw27470step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27470step1 raw27470step0; decide +kernel
      have hl : raw27470step1Labels = raw27470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27470step0 raw27470step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6553 raw6553Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6553 raw6553Labels = mixedMoment B raw6553step0 raw6553step0Labels := by
      have hz : ∀ j, raw6553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6553step0 = (fun i j => raw6553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6553step0 raw6553; decide +kernel
      have hl : raw6553step0Labels = raw6553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553 raw6553Labels permutation520 hz
    mixedMoment B raw6553step0 raw6553step0Labels = mixedMoment B raw6553step1 raw6553step1Labels := by
      have hz : ∀ j, raw6553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6553step1 = (fun i j => raw6553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6553step1 raw6553step0; decide +kernel
      have hl : raw6553step1Labels = raw6553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553step0 raw6553step0Labels permutation80 hz
    mixedMoment B raw6553step1 raw6553step1Labels = mixedMoment B raw6553step2 raw6553step2Labels := by
      have ha : raw6553step2 = (fun i j => raw6553step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6553step2 raw6553step1; decide +kernel
      have hl : raw6553step2Labels = raw6553step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6553step1 raw6553step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical6564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6564 raw6564Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw6564 raw6564Labels = mixedMoment B raw6564step0 raw6564step0Labels := by
      have hz : ∀ j, raw6564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6564step0 = (fun i j => raw6564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6564step0 raw6564; decide +kernel
      have hl : raw6564step0Labels = raw6564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6564 raw6564Labels permutation346 hz
    mixedMoment B raw6564step0 raw6564step0Labels = mixedMoment B raw6564step1 raw6564step1Labels := by
      have ha : raw6564step1 = (fun i j => raw6564step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6564step1 raw6564step0; decide +kernel
      have hl : raw6564step1Labels = raw6564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6564step0 raw6564step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical6566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6566 raw6566Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw6566 raw6566Labels = mixedMoment B raw6566step0 raw6566step0Labels := by
      have hz : ∀ j, raw6566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6566step0 = (fun i j => raw6566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6566step0 raw6566; decide +kernel
      have hl : raw6566step0Labels = raw6566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6566 raw6566Labels permutation346 hz
    _ = mixedMoment B node2495 node2495Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7199 raw7199Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7199 raw7199Labels = mixedMoment B raw7199step0 raw7199step0Labels := by
      have hz : ∀ j, raw7199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7199step0 = (fun i j => raw7199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7199step0 raw7199; decide +kernel
      have hl : raw7199step0Labels = raw7199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7199 raw7199Labels permutation520 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical7209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7209 raw7209Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7209 raw7209Labels = mixedMoment B raw7209step0 raw7209step0Labels := by
      have ha : raw7209step0 = (fun i j => raw7209 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7209step0 raw7209; decide +kernel
      have hl : raw7209step0Labels = raw7209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7209 raw7209Labels permutation160 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical7212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7212 raw7212Labels = mixedMoment B node2470 node2470Labels := by
  calc
    _ = mixedMoment B node2470 node2470Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node945 node945Labels = Sparse.eval nodeValue945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 945) = mixedMoment B node945 node945Labels := rfl
  simpa [nodeValue945, Sparse.eval] using hc.symm

theorem sound954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node954 node954Labels = Sparse.eval nodeValue954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 954) = mixedMoment B node954 node954Labels := rfl
  simpa [nodeValue954, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1112 node1112Labels = Sparse.eval nodeValue1112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1112) = mixedMoment B node1112 node1112Labels := rfl
  simpa [nodeValue1112, Sparse.eval] using hc.symm

theorem sound1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1121 node1121Labels = Sparse.eval nodeValue1121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1121) = mixedMoment B node1121 node1121Labels := rfl
  simpa [nodeValue1121, Sparse.eval] using hc.symm

theorem sound1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1132 node1132Labels = Sparse.eval nodeValue1132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1132) = mixedMoment B node1132 node1132Labels := rfl
  simpa [nodeValue1132, Sparse.eval] using hc.symm

theorem sound1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1146 node1146Labels = Sparse.eval nodeValue1146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1146) = mixedMoment B node1146 node1146Labels := rfl
  simpa [nodeValue1146, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1155 node1155Labels = Sparse.eval nodeValue1155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1155) = mixedMoment B node1155 node1155Labels := rfl
  simpa [nodeValue1155, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1317 node1317Labels = Sparse.eval nodeValue1317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1317) = mixedMoment B node1317 node1317Labels := rfl
  simpa [nodeValue1317, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1825 node1825Labels = Sparse.eval nodeValue1825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1825) = mixedMoment B node1825 node1825Labels := rfl
  simpa [nodeValue1825, Sparse.eval] using hc.symm

theorem sound1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1832 node1832Labels = Sparse.eval nodeValue1832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1832) = mixedMoment B node1832 node1832Labels := rfl
  simpa [nodeValue1832, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1903 node1903Labels = Sparse.eval nodeValue1903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1903) = mixedMoment B node1903 node1903Labels := rfl
  simpa [nodeValue1903, Sparse.eval] using hc.symm

theorem sound1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1904 node1904Labels = Sparse.eval nodeValue1904 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1904) = mixedMoment B node1904 node1904Labels := rfl
  simpa [nodeValue1904, Sparse.eval] using hc.symm

theorem sound1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1907 node1907Labels = Sparse.eval nodeValue1907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1907) = mixedMoment B node1907 node1907Labels := rfl
  simpa [nodeValue1907, Sparse.eval] using hc.symm

theorem sound1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1913 node1913Labels = Sparse.eval nodeValue1913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1913) = mixedMoment B node1913 node1913Labels := rfl
  simpa [nodeValue1913, Sparse.eval] using hc.symm

theorem sound1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1917 node1917Labels = Sparse.eval nodeValue1917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1917) = mixedMoment B node1917 node1917Labels := rfl
  simpa [nodeValue1917, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1923 node1923Labels = Sparse.eval nodeValue1923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1923) = mixedMoment B node1923 node1923Labels := rfl
  simpa [nodeValue1923, Sparse.eval] using hc.symm

theorem sound1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1925 node1925Labels = Sparse.eval nodeValue1925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1925) = mixedMoment B node1925 node1925Labels := rfl
  simpa [nodeValue1925, Sparse.eval] using hc.symm

theorem sound1927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1927 node1927Labels = Sparse.eval nodeValue1927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1927) = mixedMoment B node1927 node1927Labels := rfl
  simpa [nodeValue1927, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

theorem sound1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1949 node1949Labels = Sparse.eval nodeValue1949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1949) = mixedMoment B node1949 node1949Labels := rfl
  simpa [nodeValue1949, Sparse.eval] using hc.symm

theorem sound1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1951 node1951Labels = Sparse.eval nodeValue1951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1951) = mixedMoment B node1951 node1951Labels := rfl
  simpa [nodeValue1951, Sparse.eval] using hc.symm

theorem sound1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1973 node1973Labels = Sparse.eval nodeValue1973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1973) = mixedMoment B node1973 node1973Labels := rfl
  simpa [nodeValue1973, Sparse.eval] using hc.symm

theorem sound1980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1980 node1980Labels = Sparse.eval nodeValue1980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1980) = mixedMoment B node1980 node1980Labels := rfl
  simpa [nodeValue1980, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2113 node2113Labels = Sparse.eval nodeValue2113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2113) = mixedMoment B node2113 node2113Labels := rfl
  simpa [nodeValue2113, Sparse.eval] using hc.symm

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

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

theorem sound2196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2196 node2196Labels = Sparse.eval nodeValue2196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2196) = mixedMoment B node2196 node2196Labels := rfl
  simpa [nodeValue2196, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

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

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2320 node2320Labels = Sparse.eval nodeValue2320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2320) = mixedMoment B node2320 node2320Labels := rfl
  simpa [nodeValue2320, Sparse.eval] using hc.symm

theorem sound2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2327 node2327Labels = Sparse.eval nodeValue2327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2327) = mixedMoment B node2327 node2327Labels := rfl
  simpa [nodeValue2327, Sparse.eval] using hc.symm

theorem sound2335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2335 node2335Labels = Sparse.eval nodeValue2335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2335) = mixedMoment B node2335 node2335Labels := rfl
  simpa [nodeValue2335, Sparse.eval] using hc.symm

theorem sound2346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2346 node2346Labels = Sparse.eval nodeValue2346 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2346) = mixedMoment B node2346 node2346Labels := rfl
  simpa [nodeValue2346, Sparse.eval] using hc.symm

theorem sound2352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2352 node2352Labels = Sparse.eval nodeValue2352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2352) = mixedMoment B node2352 node2352Labels := rfl
  simpa [nodeValue2352, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2423 node2423Labels = Sparse.eval nodeValue2423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2423) = mixedMoment B node2423 node2423Labels := rfl
  simpa [nodeValue2423, Sparse.eval] using hc.symm

theorem sound2426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2426 node2426Labels = Sparse.eval nodeValue2426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2426) = mixedMoment B node2426 node2426Labels := rfl
  simpa [nodeValue2426, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

theorem sound2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2435 node2435Labels = Sparse.eval nodeValue2435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2435) = mixedMoment B node2435 node2435Labels := rfl
  simpa [nodeValue2435, Sparse.eval] using hc.symm

theorem sound2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2437 node2437Labels = Sparse.eval nodeValue2437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2437) = mixedMoment B node2437 node2437Labels := rfl
  simpa [nodeValue2437, Sparse.eval] using hc.symm

theorem sound2443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2443 node2443Labels = Sparse.eval nodeValue2443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2443) = mixedMoment B node2443 node2443Labels := rfl
  simpa [nodeValue2443, Sparse.eval] using hc.symm

theorem sound2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2470 node2470Labels = Sparse.eval nodeValue2470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2470) = mixedMoment B node2470 node2470Labels := rfl
  simpa [nodeValue2470, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

theorem sound2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2520 node2520Labels = Sparse.eval nodeValue2520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2520) = mixedMoment B node2520 node2520Labels := rfl
  simpa [nodeValue2520, Sparse.eval] using hc.symm

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

theorem sound2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2524 node2524Labels = Sparse.eval nodeValue2524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2524) = mixedMoment B node2524 node2524Labels := rfl
  simpa [nodeValue2524, Sparse.eval] using hc.symm

theorem sound2558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2558 node2558Labels = Sparse.eval nodeValue2558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2558) = mixedMoment B node2558 node2558Labels := rfl
  simpa [nodeValue2558, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2837 node2837Labels = Sparse.eval nodeValue2837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2837) = mixedMoment B node2837 node2837Labels := rfl
  simpa [nodeValue2837, Sparse.eval] using hc.symm

theorem sound2842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2842 node2842Labels = Sparse.eval nodeValue2842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2842) = mixedMoment B node2842 node2842Labels := rfl
  simpa [nodeValue2842, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3339 node3339Labels = 0 := by
  exact mixedMoment_alpha B hF node3339 node3339Labels 1 permutation437
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3339 node3339Labels = Sparse.eval nodeValue3339 (mixedVector B) := by
  simpa only [nodeValue3339, Sparse.eval_nil] using zero3339 B _hB _hF

theorem sound3343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3343 node3343Labels = Sparse.eval nodeValue3343 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3343) = mixedMoment B node3343 node3343Labels := rfl
  simpa [nodeValue3343, Sparse.eval] using hc.symm

theorem sound3355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3355 node3355Labels = Sparse.eval nodeValue3355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3355) = mixedMoment B node3355 node3355Labels := rfl
  simpa [nodeValue3355, Sparse.eval] using hc.symm

theorem sound3368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3368 node3368Labels = Sparse.eval nodeValue3368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3368) = mixedMoment B node3368 node3368Labels := rfl
  simpa [nodeValue3368, Sparse.eval] using hc.symm

theorem sound3385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3385 node3385Labels = Sparse.eval nodeValue3385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3385) = mixedMoment B node3385 node3385Labels := rfl
  simpa [nodeValue3385, Sparse.eval] using hc.symm

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

theorem sound3434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3434 node3434Labels = Sparse.eval nodeValue3434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3434) = mixedMoment B node3434 node3434Labels := rfl
  simpa [nodeValue3434, Sparse.eval] using hc.symm

theorem sound3443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3443 node3443Labels = Sparse.eval nodeValue3443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3443) = mixedMoment B node3443 node3443Labels := rfl
  simpa [nodeValue3443, Sparse.eval] using hc.symm

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

theorem sound3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3464 node3464Labels = Sparse.eval nodeValue3464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3464) = mixedMoment B node3464 node3464Labels := rfl
  simpa [nodeValue3464, Sparse.eval] using hc.symm

theorem sound3466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3466 node3466Labels = Sparse.eval nodeValue3466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3466) = mixedMoment B node3466 node3466Labels := rfl
  simpa [nodeValue3466, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3472 node3472Labels = Sparse.eval nodeValue3472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3472) = mixedMoment B node3472 node3472Labels := rfl
  simpa [nodeValue3472, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1908 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 0) (sourceB1908 + difference 0 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 0) (sourceB1908 + difference 0 0) sourceC1908) = raw27388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27388; decide +kernel
    rw [ha]
    exact (canonical27388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 1) (sourceB1908 + difference 1 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1904) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 1) (sourceB1908 + difference 1 0) sourceC1908) = raw27389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27389; decide +kernel
    rw [ha]
    exact (canonical27389 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 2) (sourceB1908 + difference 2 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1925) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 2) (sourceB1908 + difference 2 0) sourceC1908) = raw27390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27390; decide +kernel
    rw [ha]
    exact (canonical27390 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 3) (sourceB1908 + difference 3 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 3) (sourceB1908 + difference 3 0) sourceC1908) = raw27391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27391; decide +kernel
    rw [ha]
    exact (canonical27391 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 4) (sourceB1908 + difference 4 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 4) (sourceB1908 + difference 4 0) sourceC1908) = raw27392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27392; decide +kernel
    rw [ha]
    exact (canonical27392 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 5) (sourceB1908 + difference 5 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 5) (sourceB1908 + difference 5 0) sourceC1908) = raw27393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27393; decide +kernel
    rw [ha]
    exact (canonical27393 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1908 + sourceB1908) sourceC1908) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1908 + sourceB1908) sourceC1908) = raw27394 := by
      apply Matrix.ext; unfold doubleCharges sourceA1908 sourceB1908 sourceC1908 raw27394; decide +kernel
    rw [ha]
    exact (canonical27394 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1908 sourceB1908 sourceC1908
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1908, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1909 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 0) (sourceB1909 + difference 0 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 0) (sourceB1909 + difference 0 4) sourceC1909) = raw23032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw23032; decide +kernel
    rw [ha]
    exact (canonical23032 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 1) (sourceB1909 + difference 1 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1832) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 1) (sourceB1909 + difference 1 4) sourceC1909) = raw27395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27395; decide +kernel
    rw [ha]
    exact (canonical27395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 2) (sourceB1909 + difference 2 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 2) (sourceB1909 + difference 2 4) sourceC1909) = raw27396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27396; decide +kernel
    rw [ha]
    exact (canonical27396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 3) (sourceB1909 + difference 3 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 3) (sourceB1909 + difference 3 4) sourceC1909) = raw27397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27397; decide +kernel
    rw [ha]
    exact (canonical27397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 4) (sourceB1909 + difference 4 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 4) (sourceB1909 + difference 4 4) sourceC1909) = raw27398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27398; decide +kernel
    rw [ha]
    exact (canonical27398 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 5) (sourceB1909 + difference 5 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 5) (sourceB1909 + difference 5 4) sourceC1909) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1909 + sourceB1909) sourceC1909) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1909 + sourceB1909) sourceC1909) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1909 sourceB1909 sourceC1909 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1909 sourceB1909 sourceC1909
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1909, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1910 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 0) (sourceB1910 + difference 0 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 0) (sourceB1910 + difference 0 3) sourceC1910) = raw25240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw25240; decide +kernel
    rw [ha]
    exact (canonical25240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 1) (sourceB1910 + difference 1 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1825) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 1) (sourceB1910 + difference 1 3) sourceC1910) = raw27399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27399; decide +kernel
    rw [ha]
    exact (canonical27399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 2) (sourceB1910 + difference 2 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 2) (sourceB1910 + difference 2 3) sourceC1910) = raw27400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27400; decide +kernel
    rw [ha]
    exact (canonical27400 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 3) (sourceB1910 + difference 3 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 3) (sourceB1910 + difference 3 3) sourceC1910) = raw27401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27401; decide +kernel
    rw [ha]
    exact (canonical27401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 4) (sourceB1910 + difference 4 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 4) (sourceB1910 + difference 4 3) sourceC1910) = raw27402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27402; decide +kernel
    rw [ha]
    exact (canonical27402 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 5) (sourceB1910 + difference 5 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 5) (sourceB1910 + difference 5 3) sourceC1910) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1910 + sourceB1910) sourceC1910) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1910 + sourceB1910) sourceC1910) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1910 sourceB1910 sourceC1910 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1910 sourceB1910 sourceC1910
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1910, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1911 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1911 + difference 0 1) (sourceB1911 + difference 1 0) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1911 + difference 0 1) (sourceB1911 + difference 1 0) sourceC1911) = raw27403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27403; decide +kernel
    rw [ha]
    exact (canonical27403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1911 + difference 1 1) (sourceB1911 + difference 1 1) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1911 + difference 1 1) (sourceB1911 + difference 1 1) sourceC1911) = raw27404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27404; decide +kernel
    rw [ha]
    exact (canonical27404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1911 + difference 2 1) (sourceB1911 + difference 1 2) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA1911 + difference 2 1) (sourceB1911 + difference 1 2) sourceC1911) = raw27405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27405; decide +kernel
    rw [ha]
    exact (canonical27405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1911 + difference 3 1) (sourceB1911 + difference 1 3) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA1911 + difference 3 1) (sourceB1911 + difference 1 3) sourceC1911) = raw27406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27406; decide +kernel
    rw [ha]
    exact (canonical27406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1911 + difference 4 1) (sourceB1911 + difference 1 4) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA1911 + difference 4 1) (sourceB1911 + difference 1 4) sourceC1911) = raw27407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27407; decide +kernel
    rw [ha]
    exact (canonical27407 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1911 + difference 5 1) (sourceB1911 + difference 1 5) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1911 + difference 5 1) (sourceB1911 + difference 1 5) sourceC1911) = raw27408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27408; decide +kernel
    rw [ha]
    exact (canonical27408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1911 + sourceB1911) sourceC1911) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1911 + sourceB1911) sourceC1911) = raw27409 := by
      apply Matrix.ext; unfold doubleCharges sourceA1911 sourceB1911 sourceC1911 raw27409; decide +kernel
    rw [ha]
    exact (canonical27409 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1911 sourceB1911 sourceC1911
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1911, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1912 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 0) (sourceB1912 + difference 0 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 0) (sourceB1912 + difference 0 0) sourceC1912) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 1) (sourceB1912 + difference 1 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 1) (sourceB1912 + difference 1 0) sourceC1912) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 2) (sourceB1912 + difference 2 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 2) (sourceB1912 + difference 2 0) sourceC1912) = raw27410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27410; decide +kernel
    rw [ha]
    exact (canonical27410 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 3) (sourceB1912 + difference 3 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 3) (sourceB1912 + difference 3 0) sourceC1912) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 4) (sourceB1912 + difference 4 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 4) (sourceB1912 + difference 4 0) sourceC1912) = raw27412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27412; decide +kernel
    rw [ha]
    exact (canonical27412 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 5) (sourceB1912 + difference 5 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 5) (sourceB1912 + difference 5 0) sourceC1912) = raw27413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27413; decide +kernel
    rw [ha]
    exact (canonical27413 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1912 + sourceB1912) sourceC1912) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1912 + sourceB1912) sourceC1912) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1912 sourceB1912 sourceC1912 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1912 sourceB1912 sourceC1912
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1912, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1913 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1913 + difference 0 3) (sourceB1913 + difference 3 0) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1913 + difference 0 3) (sourceB1913 + difference 3 0) sourceC1913) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1913 + difference 1 3) (sourceB1913 + difference 3 1) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1913 + difference 1 3) (sourceB1913 + difference 3 1) sourceC1913) = raw27414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27414; decide +kernel
    rw [ha]
    exact (canonical27414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1913 + difference 2 3) (sourceB1913 + difference 3 2) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1913 + difference 2 3) (sourceB1913 + difference 3 2) sourceC1913) = raw27415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27415; decide +kernel
    rw [ha]
    exact (canonical27415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1913 + difference 3 3) (sourceB1913 + difference 3 3) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1913 + difference 3 3) (sourceB1913 + difference 3 3) sourceC1913) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1913 + difference 4 3) (sourceB1913 + difference 3 4) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1913 + difference 4 3) (sourceB1913 + difference 3 4) sourceC1913) = raw27416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27416; decide +kernel
    rw [ha]
    exact (canonical27416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1913 + difference 5 3) (sourceB1913 + difference 3 5) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1913 + difference 5 3) (sourceB1913 + difference 3 5) sourceC1913) = raw27417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27417; decide +kernel
    rw [ha]
    exact (canonical27417 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1913 + sourceB1913) sourceC1913) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1913 + sourceB1913) sourceC1913) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1913 sourceB1913 sourceC1913 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1913 sourceB1913 sourceC1913
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1913, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1914 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 0) (sourceB1914 + difference 0 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 0) (sourceB1914 + difference 0 0) sourceC1914) = raw27418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27418; decide +kernel
    rw [ha]
    exact (canonical27418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 1) (sourceB1914 + difference 1 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 1) (sourceB1914 + difference 1 0) sourceC1914) = raw27419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27419; decide +kernel
    rw [ha]
    exact (canonical27419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 2) (sourceB1914 + difference 2 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1923) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 2) (sourceB1914 + difference 2 0) sourceC1914) = raw27420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27420; decide +kernel
    rw [ha]
    exact (canonical27420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 3) (sourceB1914 + difference 3 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 3) (sourceB1914 + difference 3 0) sourceC1914) = raw27421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27421; decide +kernel
    rw [ha]
    exact (canonical27421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 4) (sourceB1914 + difference 4 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 4) (sourceB1914 + difference 4 0) sourceC1914) = raw27422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27422; decide +kernel
    rw [ha]
    exact (canonical27422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 5) (sourceB1914 + difference 5 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 5) (sourceB1914 + difference 5 0) sourceC1914) = raw27423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27423; decide +kernel
    rw [ha]
    exact (canonical27423 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1914 + sourceB1914) sourceC1914) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1914 + sourceB1914) sourceC1914) = raw27424 := by
      apply Matrix.ext; unfold doubleCharges sourceA1914 sourceB1914 sourceC1914 raw27424; decide +kernel
    rw [ha]
    exact (canonical27424 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1914 sourceB1914 sourceC1914
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1914, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1915 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1915 + difference 0 1) (sourceB1915 + difference 1 0) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1915 + difference 0 1) (sourceB1915 + difference 1 0) sourceC1915) = raw27425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27425; decide +kernel
    rw [ha]
    exact (canonical27425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1915 + difference 1 1) (sourceB1915 + difference 1 1) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA1915 + difference 1 1) (sourceB1915 + difference 1 1) sourceC1915) = raw27426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27426; decide +kernel
    rw [ha]
    exact (canonical27426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1915 + difference 2 1) (sourceB1915 + difference 1 2) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA1915 + difference 2 1) (sourceB1915 + difference 1 2) sourceC1915) = raw27427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27427; decide +kernel
    rw [ha]
    exact (canonical27427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1915 + difference 3 1) (sourceB1915 + difference 1 3) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA1915 + difference 3 1) (sourceB1915 + difference 1 3) sourceC1915) = raw27428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27428; decide +kernel
    rw [ha]
    exact (canonical27428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1915 + difference 4 1) (sourceB1915 + difference 1 4) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA1915 + difference 4 1) (sourceB1915 + difference 1 4) sourceC1915) = raw27429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27429; decide +kernel
    rw [ha]
    exact (canonical27429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1915 + difference 5 1) (sourceB1915 + difference 1 5) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1915 + difference 5 1) (sourceB1915 + difference 1 5) sourceC1915) = raw27430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27430; decide +kernel
    rw [ha]
    exact (canonical27430 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1915 + sourceB1915) sourceC1915) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1915 + sourceB1915) sourceC1915) = raw27431 := by
      apply Matrix.ext; unfold doubleCharges sourceA1915 sourceB1915 sourceC1915 raw27431; decide +kernel
    rw [ha]
    exact (canonical27431 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1915 sourceB1915 sourceC1915
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1915, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1916 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 0) (sourceB1916 + difference 0 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 0) (sourceB1916 + difference 0 0) sourceC1916) = raw27414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27414; decide +kernel
    rw [ha]
    exact (canonical27414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 1) (sourceB1916 + difference 1 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 1) (sourceB1916 + difference 1 0) sourceC1916) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 2) (sourceB1916 + difference 2 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 2) (sourceB1916 + difference 2 0) sourceC1916) = raw27432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27432; decide +kernel
    rw [ha]
    exact (canonical27432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 3) (sourceB1916 + difference 3 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 3) (sourceB1916 + difference 3 0) sourceC1916) = raw27433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27433; decide +kernel
    rw [ha]
    exact (canonical27433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 4) (sourceB1916 + difference 4 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 4) (sourceB1916 + difference 4 0) sourceC1916) = raw27434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27434; decide +kernel
    rw [ha]
    exact (canonical27434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 5) (sourceB1916 + difference 5 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 5) (sourceB1916 + difference 5 0) sourceC1916) = raw27435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27435; decide +kernel
    rw [ha]
    exact (canonical27435 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1916 + sourceB1916) sourceC1916) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1916 + sourceB1916) sourceC1916) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1916 sourceB1916 sourceC1916 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1916 sourceB1916 sourceC1916
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1916, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1917 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 0) (sourceB1917 + difference 0 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 0) (sourceB1917 + difference 0 3) sourceC1917) = raw27436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27436; decide +kernel
    rw [ha]
    exact (canonical27436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 1) (sourceB1917 + difference 1 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2335) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 1) (sourceB1917 + difference 1 3) sourceC1917) = raw27437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27437; decide +kernel
    rw [ha]
    exact (canonical27437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 2) (sourceB1917 + difference 2 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 2) (sourceB1917 + difference 2 3) sourceC1917) = raw27438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27438; decide +kernel
    rw [ha]
    exact (canonical27438 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 3) (sourceB1917 + difference 3 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 3) (sourceB1917 + difference 3 3) sourceC1917) = raw6566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw6566; decide +kernel
    rw [ha]
    exact (canonical6566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 4) (sourceB1917 + difference 4 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 4) (sourceB1917 + difference 4 3) sourceC1917) = raw27439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27439; decide +kernel
    rw [ha]
    exact (canonical27439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 5) (sourceB1917 + difference 5 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 5) (sourceB1917 + difference 5 3) sourceC1917) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1917 + sourceB1917) sourceC1917) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1917 + sourceB1917) sourceC1917) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA1917 sourceB1917 sourceC1917 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1917 sourceB1917 sourceC1917
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1917, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1918 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 0) (sourceB1918 + difference 0 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 0) (sourceB1918 + difference 0 0) sourceC1918) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 1) (sourceB1918 + difference 1 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 1) (sourceB1918 + difference 1 0) sourceC1918) = raw27440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27440; decide +kernel
    rw [ha]
    exact (canonical27440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 2) (sourceB1918 + difference 2 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 2) (sourceB1918 + difference 2 0) sourceC1918) = raw27441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27441; decide +kernel
    rw [ha]
    exact (canonical27441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 3) (sourceB1918 + difference 3 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 3) (sourceB1918 + difference 3 0) sourceC1918) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 4) (sourceB1918 + difference 4 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 4) (sourceB1918 + difference 4 0) sourceC1918) = raw27443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27443; decide +kernel
    rw [ha]
    exact (canonical27443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 5) (sourceB1918 + difference 5 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 5) (sourceB1918 + difference 5 0) sourceC1918) = raw27444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27444; decide +kernel
    rw [ha]
    exact (canonical27444 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1918 + sourceB1918) sourceC1918) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1918 + sourceB1918) sourceC1918) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1918 sourceB1918 sourceC1918 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1918 sourceB1918 sourceC1918
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1918, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1919 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1919 + difference 0 3) (sourceB1919 + difference 3 0) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1919 + difference 0 3) (sourceB1919 + difference 3 0) sourceC1919) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1919 + difference 1 3) (sourceB1919 + difference 3 1) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1919 + difference 1 3) (sourceB1919 + difference 3 1) sourceC1919) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1919 + difference 2 3) (sourceB1919 + difference 3 2) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1919 + difference 2 3) (sourceB1919 + difference 3 2) sourceC1919) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1919 + difference 3 3) (sourceB1919 + difference 3 3) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1919 + difference 3 3) (sourceB1919 + difference 3 3) sourceC1919) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1919 + difference 4 3) (sourceB1919 + difference 3 4) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1919 + difference 4 3) (sourceB1919 + difference 3 4) sourceC1919) = raw27445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27445; decide +kernel
    rw [ha]
    exact (canonical27445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1919 + difference 5 3) (sourceB1919 + difference 3 5) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1919 + difference 5 3) (sourceB1919 + difference 3 5) sourceC1919) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1919 + sourceB1919) sourceC1919) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1919 + sourceB1919) sourceC1919) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1919 sourceB1919 sourceC1919 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1919 sourceB1919 sourceC1919
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1919, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources60
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1920 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 0) (sourceB1920 + difference 0 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 0) (sourceB1920 + difference 0 2) sourceC1920) = raw27447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27447; decide +kernel
    rw [ha]
    exact (canonical27447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 1) (sourceB1920 + difference 1 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 1) (sourceB1920 + difference 1 2) sourceC1920) = raw27448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27448; decide +kernel
    rw [ha]
    exact (canonical27448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 2) (sourceB1920 + difference 2 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 2) (sourceB1920 + difference 2 2) sourceC1920) = raw7212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw7212; decide +kernel
    rw [ha]
    exact (canonical7212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 3) (sourceB1920 + difference 3 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 3) (sourceB1920 + difference 3 2) sourceC1920) = raw27449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27449; decide +kernel
    rw [ha]
    exact (canonical27449 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 4) (sourceB1920 + difference 4 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 4) (sourceB1920 + difference 4 2) sourceC1920) = raw27450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27450; decide +kernel
    rw [ha]
    exact (canonical27450 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 5) (sourceB1920 + difference 5 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 5) (sourceB1920 + difference 5 2) sourceC1920) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1920 + sourceB1920) sourceC1920) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1920 + sourceB1920) sourceC1920) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA1920 sourceB1920 sourceC1920 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1920 sourceB1920 sourceC1920
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1920, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1921 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 0) (sourceB1921 + difference 0 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 0) (sourceB1921 + difference 0 0) sourceC1921) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 1) (sourceB1921 + difference 1 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 1) (sourceB1921 + difference 1 0) sourceC1921) = raw27451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27451; decide +kernel
    rw [ha]
    exact (canonical27451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 2) (sourceB1921 + difference 2 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 2) (sourceB1921 + difference 2 0) sourceC1921) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 3) (sourceB1921 + difference 3 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 3) (sourceB1921 + difference 3 0) sourceC1921) = raw27452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27452; decide +kernel
    rw [ha]
    exact (canonical27452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 4) (sourceB1921 + difference 4 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3339) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 4) (sourceB1921 + difference 4 0) sourceC1921) = raw27453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27453; decide +kernel
    rw [ha]
    exact (canonical27453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 5) (sourceB1921 + difference 5 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 5) (sourceB1921 + difference 5 0) sourceC1921) = raw27454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27454; decide +kernel
    rw [ha]
    exact (canonical27454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1921 + sourceB1921) sourceC1921) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1921 + sourceB1921) sourceC1921) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1921 sourceB1921 sourceC1921 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1921 sourceB1921 sourceC1921
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1921, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1923 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1923 + difference 0 2) (sourceB1923 + difference 2 0) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1923 + difference 0 2) (sourceB1923 + difference 2 0) sourceC1923) = raw27460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27460; decide +kernel
    rw [ha]
    exact (canonical27460 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1923 + difference 1 2) (sourceB1923 + difference 2 1) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1923 + difference 1 2) (sourceB1923 + difference 2 1) sourceC1923) = raw27461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27461; decide +kernel
    rw [ha]
    exact (canonical27461 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1923 + difference 2 2) (sourceB1923 + difference 2 2) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA1923 + difference 2 2) (sourceB1923 + difference 2 2) sourceC1923) = raw27462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27462; decide +kernel
    rw [ha]
    exact (canonical27462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1923 + difference 3 2) (sourceB1923 + difference 2 3) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA1923 + difference 3 2) (sourceB1923 + difference 2 3) sourceC1923) = raw27463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27463; decide +kernel
    rw [ha]
    exact (canonical27463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1923 + difference 4 2) (sourceB1923 + difference 2 4) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1923 + difference 4 2) (sourceB1923 + difference 2 4) sourceC1923) = raw27464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27464; decide +kernel
    rw [ha]
    exact (canonical27464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1923 + difference 5 2) (sourceB1923 + difference 2 5) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1923 + difference 5 2) (sourceB1923 + difference 2 5) sourceC1923) = raw27465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27465; decide +kernel
    rw [ha]
    exact (canonical27465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1923 + sourceB1923) sourceC1923) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1923 + sourceB1923) sourceC1923) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA1923 sourceB1923 sourceC1923 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1923 sourceB1923 sourceC1923
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1923, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1924 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 0) (sourceB1924 + difference 0 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 0) (sourceB1924 + difference 0 4) sourceC1924) = raw27467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27467; decide +kernel
    rw [ha]
    exact (canonical27467 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 1) (sourceB1924 + difference 1 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 1) (sourceB1924 + difference 1 4) sourceC1924) = raw27468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27468; decide +kernel
    rw [ha]
    exact (canonical27468 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 2) (sourceB1924 + difference 2 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 2) (sourceB1924 + difference 2 4) sourceC1924) = raw27464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27464; decide +kernel
    rw [ha]
    exact (canonical27464 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 3) (sourceB1924 + difference 3 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 3) (sourceB1924 + difference 3 4) sourceC1924) = raw27469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27469; decide +kernel
    rw [ha]
    exact (canonical27469 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 4) (sourceB1924 + difference 4 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 4) (sourceB1924 + difference 4 4) sourceC1924) = raw27462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27462; decide +kernel
    rw [ha]
    exact (canonical27462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 5) (sourceB1924 + difference 5 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 5) (sourceB1924 + difference 5 4) sourceC1924) = raw27470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27470; decide +kernel
    rw [ha]
    exact (canonical27470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1924 + sourceB1924) sourceC1924) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1924 + sourceB1924) sourceC1924) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA1924 sourceB1924 sourceC1924 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1924 sourceB1924 sourceC1924
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1924, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1616 : Integer.Sparse.reindex keyMap MixedData.row1616 = numericRow1616 := by decide +kernel

theorem numericCheck1616 (x : Master → ℝ) : Integer.Sparse.eval numericRow1616 x =
    (1 : ℝ) * reducedSource1616 x := by
  norm_num [numericRow1616, reducedSource1616, Integer.Sparse.eval, Sparse.eval, nodeValue1903, nodeValue1904, nodeValue1913, nodeValue1925, nodeValue2196, nodeValue3464, nodeValue4080]

theorem reindexCheck1617 : Integer.Sparse.reindex keyMap MixedData.row1617 = numericRow1617 := by decide +kernel

theorem numericCheck1617 (x : Master → ℝ) : Integer.Sparse.eval numericRow1617 x =
    (1 : ℝ) * reducedSource1617 x := by
  norm_num [numericRow1617, reducedSource1617, Integer.Sparse.eval, Sparse.eval, nodeValue954, nodeValue1832, nodeValue1980, nodeValue2113, nodeValue2115, nodeValue4084]

theorem reindexCheck1618 : Integer.Sparse.reindex keyMap MixedData.row1618 = numericRow1618 := by decide +kernel

theorem numericCheck1618 (x : Master → ℝ) : Integer.Sparse.eval numericRow1618 x =
    (1 : ℝ) * reducedSource1618 x := by
  norm_num [numericRow1618, reducedSource1618, Integer.Sparse.eval, Sparse.eval, nodeValue945, nodeValue1825, nodeValue1973, nodeValue2090, nodeValue2107, nodeValue2112, nodeValue4083]

theorem reindexCheck1619 : Integer.Sparse.reindex keyMap MixedData.row1619 = numericRow1619 := by decide +kernel

theorem numericCheck1619 (x : Master → ℝ) : Integer.Sparse.eval numericRow1619 x =
    (1 : ℝ) * reducedSource1619 x := by
  norm_num [numericRow1619, reducedSource1619, Integer.Sparse.eval, Sparse.eval, nodeValue1121, nodeValue2327, nodeValue2423, nodeValue2443, nodeValue2486, nodeValue2488, nodeValue4092]

theorem reindexCheck1620 : Integer.Sparse.reindex keyMap MixedData.row1620 = numericRow1620 := by decide +kernel

theorem numericCheck1620 (x : Master → ℝ) : Integer.Sparse.eval numericRow1620 x =
    (1 : ℝ) * reducedSource1620 x := by
  norm_num [numericRow1620, reducedSource1620, Integer.Sparse.eval, Sparse.eval, nodeValue1946, nodeValue2259, nodeValue3355, nodeValue3434, nodeValue3481, nodeValue3486, nodeValue4081]

theorem reindexCheck1621 : Integer.Sparse.reindex keyMap MixedData.row1621 = numericRow1621 := by decide +kernel

theorem numericCheck1621 (x : Master → ℝ) : Integer.Sparse.eval numericRow1621 x =
    (1 : ℝ) * reducedSource1621 x := by
  norm_num [numericRow1621, reducedSource1621, Integer.Sparse.eval, Sparse.eval, nodeValue2259, nodeValue2261, nodeValue2267, nodeValue2287, nodeValue3486, nodeValue4081]

theorem reindexCheck1622 : Integer.Sparse.reindex keyMap MixedData.row1622 = numericRow1622 := by decide +kernel

theorem numericCheck1622 (x : Master → ℝ) : Integer.Sparse.eval numericRow1622 x =
    (1 : ℝ) * reducedSource1622 x := by
  norm_num [numericRow1622, reducedSource1622, Integer.Sparse.eval, Sparse.eval, nodeValue1923, nodeValue1927, nodeValue1928, nodeValue1949, nodeValue2217, nodeValue3480, nodeValue4082]

theorem reindexCheck1623 : Integer.Sparse.reindex keyMap MixedData.row1623 = numericRow1623 := by decide +kernel

theorem numericCheck1623 (x : Master → ℝ) : Integer.Sparse.eval numericRow1623 x =
    (1 : ℝ) * reducedSource1623 x := by
  norm_num [numericRow1623, reducedSource1623, Integer.Sparse.eval, Sparse.eval, nodeValue1146, nodeValue2346, nodeValue2435, nodeValue2520, nodeValue2522, nodeValue4084]

theorem reindexCheck1624 : Integer.Sparse.reindex keyMap MixedData.row1624 = numericRow1624 := by decide +kernel

theorem numericCheck1624 (x : Master → ℝ) : Integer.Sparse.eval numericRow1624 x =
    (1 : ℝ) * reducedSource1624 x := by
  norm_num [numericRow1624, reducedSource1624, Integer.Sparse.eval, Sparse.eval, nodeValue1951, nodeValue2267, nodeValue2837, nodeValue2842, nodeValue3486, nodeValue4081]

theorem reindexCheck1625 : Integer.Sparse.reindex keyMap MixedData.row1625 = numericRow1625 := by decide +kernel

theorem numericCheck1625 (x : Master → ℝ) : Integer.Sparse.eval numericRow1625 x =
    (1 : ℝ) * reducedSource1625 x := by
  norm_num [numericRow1625, reducedSource1625, Integer.Sparse.eval, Sparse.eval, nodeValue1132, nodeValue2335, nodeValue2426, nodeValue2495, nodeValue2512, nodeValue2519, nodeValue4092]

theorem reindexCheck1626 : Integer.Sparse.reindex keyMap MixedData.row1626 = numericRow1626 := by decide +kernel

theorem numericCheck1626 (x : Master → ℝ) : Integer.Sparse.eval numericRow1626 x =
    (1 : ℝ) * reducedSource1626 x := by
  norm_num [numericRow1626, reducedSource1626, Integer.Sparse.eval, Sparse.eval, nodeValue1917, nodeValue3343, nodeValue3368, nodeValue3385, nodeValue3468, nodeValue3472, nodeValue4081]

theorem reindexCheck1627 : Integer.Sparse.reindex keyMap MixedData.row1627 = numericRow1627 := by decide +kernel

theorem numericCheck1627 (x : Master → ℝ) : Integer.Sparse.eval numericRow1627 x =
    (1 : ℝ) * reducedSource1627 x := by
  norm_num [numericRow1627, reducedSource1627, Integer.Sparse.eval, Sparse.eval, nodeValue3466, nodeValue3468, nodeValue3472, nodeValue3481, nodeValue4081]

theorem reindexCheck1628 : Integer.Sparse.reindex keyMap MixedData.row1628 = numericRow1628 := by decide +kernel

theorem numericCheck1628 (x : Master → ℝ) : Integer.Sparse.eval numericRow1628 x =
    (1 : ℝ) * reducedSource1628 x := by
  norm_num [numericRow1628, reducedSource1628, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue2320, nodeValue2437, nodeValue2470, nodeValue2480, nodeValue2485, nodeValue4091]

theorem reindexCheck1629 : Integer.Sparse.reindex keyMap MixedData.row1629 = numericRow1629 := by decide +kernel

theorem numericCheck1629 (x : Master → ℝ) : Integer.Sparse.eval numericRow1629 x =
    (1 : ℝ) * reducedSource1629 x := by
  norm_num [numericRow1629, reducedSource1629, Integer.Sparse.eval, Sparse.eval, nodeValue1907, nodeValue3339, nodeValue3443, nodeValue3466, nodeValue3468, nodeValue4081]

theorem reindexCheck1630 : Integer.Sparse.reindex keyMap MixedData.row1630 = numericRow1630 := by decide +kernel

theorem numericCheck1630 (x : Master → ℝ) : Integer.Sparse.eval numericRow1630 x =
    (1 : ℝ) * reducedSource1630 x := by
  norm_num [numericRow1630, reducedSource1630, Integer.Sparse.eval, Sparse.eval, nodeValue1317, nodeValue2426, nodeValue2434, nodeValue2519, nodeValue2558, nodeValue2881, nodeValue4092]

theorem reindexCheck1631 : Integer.Sparse.reindex keyMap MixedData.row1631 = numericRow1631 := by decide +kernel

theorem numericCheck1631 (x : Master → ℝ) : Integer.Sparse.eval numericRow1631 x =
    (1 : ℝ) * reducedSource1631 x := by
  norm_num [numericRow1631, reducedSource1631, Integer.Sparse.eval, Sparse.eval, nodeValue1155, nodeValue2352, nodeValue2434, nodeValue2524, nodeValue2558, nodeValue2561, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1616 (mixedVector B) = 0 := by
  have h1903 : mixedVector B (Sum.inr 1903) = Sparse.eval nodeValue1903 (mixedVector B) := by
    change mixedMoment B node1903 node1903Labels = _
    exact sound1903 B hB hF
  have h1904 : mixedVector B (Sum.inr 1904) = Sparse.eval nodeValue1904 (mixedVector B) := by
    change mixedMoment B node1904 node1904Labels = _
    exact sound1904 B hB hF
  have h1913 : mixedVector B (Sum.inr 1913) = Sparse.eval nodeValue1913 (mixedVector B) := by
    change mixedMoment B node1913 node1913Labels = _
    exact sound1913 B hB hF
  have h1925 : mixedVector B (Sum.inr 1925) = Sparse.eval nodeValue1925 (mixedVector B) := by
    change mixedMoment B node1925 node1925Labels = _
    exact sound1925 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1908, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1903, h1904, h1913, h1925, h2196, h3464, h4080, reducedSource1616] using sourceEq1908 B hB

theorem rowSound1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1616 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1616, numericCheck1616, reducedZero1616 B hB hF, mul_zero]

theorem reducedZero1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1617 (mixedVector B) = 0 := by
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1832 : mixedVector B (Sum.inr 1832) = Sparse.eval nodeValue1832 (mixedVector B) := by
    change mixedMoment B node1832 node1832Labels = _
    exact sound1832 B hB hF
  have h1980 : mixedVector B (Sum.inr 1980) = Sparse.eval nodeValue1980 (mixedVector B) := by
    change mixedMoment B node1980 node1980Labels = _
    exact sound1980 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1909, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h954, h1832, h1980, h2113, h2115, h4084, reducedSource1617] using sourceEq1909 B hB

theorem rowSound1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1617 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1617, numericCheck1617, reducedZero1617 B hB hF, mul_zero]

theorem reducedZero1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1618 (mixedVector B) = 0 := by
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h1825 : mixedVector B (Sum.inr 1825) = Sparse.eval nodeValue1825 (mixedVector B) := by
    change mixedMoment B node1825 node1825Labels = _
    exact sound1825 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1910, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h945, h1825, h1973, h2090, h2107, h2112, h4083, reducedSource1618] using sourceEq1910 B hB

theorem rowSound1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1618 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1618, numericCheck1618, reducedZero1618 B hB hF, mul_zero]

theorem reducedZero1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1619 (mixedVector B) = 0 := by
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1911, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1121, h2327, h2423, h2443, h2486, h2488, h4092, reducedSource1619] using sourceEq1911 B hB

theorem rowSound1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1619 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1619, numericCheck1619, reducedZero1619 B hB hF, mul_zero]

theorem reducedZero1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1620 (mixedVector B) = 0 := by
  have h1946 : mixedVector B (Sum.inr 1946) = Sparse.eval nodeValue1946 (mixedVector B) := by
    change mixedMoment B node1946 node1946Labels = _
    exact sound1946 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3355 : mixedVector B (Sum.inr 3355) = Sparse.eval nodeValue3355 (mixedVector B) := by
    change mixedMoment B node3355 node3355Labels = _
    exact sound3355 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1912, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1946, h2259, h3355, h3434, h3481, h3486, h4081, reducedSource1620] using sourceEq1912 B hB

theorem rowSound1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1620 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1620, numericCheck1620, reducedZero1620 B hB hF, mul_zero]

theorem reducedZero1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1621 (mixedVector B) = 0 := by
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1913, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2259, h2261, h2267, h2287, h3486, h4081, reducedSource1621] using sourceEq1913 B hB

theorem rowSound1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1621 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1621, numericCheck1621, reducedZero1621 B hB hF, mul_zero]

theorem reducedZero1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1622 (mixedVector B) = 0 := by
  have h1923 : mixedVector B (Sum.inr 1923) = Sparse.eval nodeValue1923 (mixedVector B) := by
    change mixedMoment B node1923 node1923Labels = _
    exact sound1923 B hB hF
  have h1927 : mixedVector B (Sum.inr 1927) = Sparse.eval nodeValue1927 (mixedVector B) := by
    change mixedMoment B node1927 node1927Labels = _
    exact sound1927 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1949 : mixedVector B (Sum.inr 1949) = Sparse.eval nodeValue1949 (mixedVector B) := by
    change mixedMoment B node1949 node1949Labels = _
    exact sound1949 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1914, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1923, h1927, h1928, h1949, h2217, h3480, h4082, reducedSource1622] using sourceEq1914 B hB

theorem rowSound1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1622 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1622, numericCheck1622, reducedZero1622 B hB hF, mul_zero]

theorem reducedZero1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1623 (mixedVector B) = 0 := by
  have h1146 : mixedVector B (Sum.inr 1146) = Sparse.eval nodeValue1146 (mixedVector B) := by
    change mixedMoment B node1146 node1146Labels = _
    exact sound1146 B hB hF
  have h2346 : mixedVector B (Sum.inr 2346) = Sparse.eval nodeValue2346 (mixedVector B) := by
    change mixedMoment B node2346 node2346Labels = _
    exact sound2346 B hB hF
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1915, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1146, h2346, h2435, h2520, h2522, h4084, reducedSource1623] using sourceEq1915 B hB

theorem rowSound1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1623 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1623, numericCheck1623, reducedZero1623 B hB hF, mul_zero]

theorem reducedZero1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1624 (mixedVector B) = 0 := by
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1916, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1951, h2267, h2837, h2842, h3486, h4081, reducedSource1624] using sourceEq1916 B hB

theorem rowSound1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1624 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1624, numericCheck1624, reducedZero1624 B hB hF, mul_zero]

theorem reducedZero1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1625 (mixedVector B) = 0 := by
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h2335 : mixedVector B (Sum.inr 2335) = Sparse.eval nodeValue2335 (mixedVector B) := by
    change mixedMoment B node2335 node2335Labels = _
    exact sound2335 B hB hF
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1917, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1132, h2335, h2426, h2495, h2512, h2519, h4092, reducedSource1625] using sourceEq1917 B hB

theorem rowSound1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1625 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1625, numericCheck1625, reducedZero1625 B hB hF, mul_zero]

theorem reducedZero1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1626 (mixedVector B) = 0 := by
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h3343 : mixedVector B (Sum.inr 3343) = Sparse.eval nodeValue3343 (mixedVector B) := by
    change mixedMoment B node3343 node3343Labels = _
    exact sound3343 B hB hF
  have h3368 : mixedVector B (Sum.inr 3368) = Sparse.eval nodeValue3368 (mixedVector B) := by
    change mixedMoment B node3368 node3368Labels = _
    exact sound3368 B hB hF
  have h3385 : mixedVector B (Sum.inr 3385) = Sparse.eval nodeValue3385 (mixedVector B) := by
    change mixedMoment B node3385 node3385Labels = _
    exact sound3385 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1918, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1917, h3343, h3368, h3385, h3468, h3472, h4081, reducedSource1626] using sourceEq1918 B hB

theorem rowSound1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1626 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1626, numericCheck1626, reducedZero1626 B hB hF, mul_zero]

theorem reducedZero1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1627 (mixedVector B) = 0 := by
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1919, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3466, h3468, h3472, h3481, h4081, reducedSource1627] using sourceEq1919 B hB

theorem rowSound1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1627 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1627, numericCheck1627, reducedZero1627 B hB hF, mul_zero]

theorem reducedZero1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1628 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1920, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h2320, h2437, h2470, h2480, h2485, h4091, reducedSource1628] using sourceEq1920 B hB

theorem rowSound1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1628 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1628, numericCheck1628, reducedZero1628 B hB hF, mul_zero]

theorem reducedZero1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1629 (mixedVector B) = 0 := by
  have h1907 : mixedVector B (Sum.inr 1907) = Sparse.eval nodeValue1907 (mixedVector B) := by
    change mixedMoment B node1907 node1907Labels = _
    exact sound1907 B hB hF
  have h3339 : mixedVector B (Sum.inr 3339) = Sparse.eval nodeValue3339 (mixedVector B) := by
    change mixedMoment B node3339 node3339Labels = _
    exact sound3339 B hB hF
  have h3443 : mixedVector B (Sum.inr 3443) = Sparse.eval nodeValue3443 (mixedVector B) := by
    change mixedMoment B node3443 node3443Labels = _
    exact sound3443 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1921, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1907, h3339, h3443, h3466, h3468, h4081, reducedSource1629] using sourceEq1921 B hB

theorem rowSound1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1629 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1629, numericCheck1629, reducedZero1629 B hB hF, mul_zero]

theorem reducedZero1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1630 (mixedVector B) = 0 := by
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1923, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1317, h2426, h2434, h2519, h2558, h2881, h4092, reducedSource1630] using sourceEq1923 B hB

theorem rowSound1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1630 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1630, numericCheck1630, reducedZero1630 B hB hF, mul_zero]

theorem reducedZero1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1631 (mixedVector B) = 0 := by
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1924, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1155, h2352, h2434, h2524, h2558, h2561, h4092, reducedSource1631] using sourceEq1924 B hB

theorem rowSound1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1631 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1631, numericCheck1631, reducedZero1631 B hB hF, mul_zero]

theorem sourceRowsAt1616 : MixedData.sourceRows (1616 : Fin 2425) =
    MixedData.row1616 := by decide +kernel

theorem sourceRowsAt1617 : MixedData.sourceRows (1617 : Fin 2425) =
    MixedData.row1617 := by decide +kernel

theorem sourceRowsAt1618 : MixedData.sourceRows (1618 : Fin 2425) =
    MixedData.row1618 := by decide +kernel

theorem sourceRowsAt1619 : MixedData.sourceRows (1619 : Fin 2425) =
    MixedData.row1619 := by decide +kernel

theorem sourceRowsAt1620 : MixedData.sourceRows (1620 : Fin 2425) =
    MixedData.row1620 := by decide +kernel

theorem sourceRowsAt1621 : MixedData.sourceRows (1621 : Fin 2425) =
    MixedData.row1621 := by decide +kernel

theorem sourceRowsAt1622 : MixedData.sourceRows (1622 : Fin 2425) =
    MixedData.row1622 := by decide +kernel

theorem sourceRowsAt1623 : MixedData.sourceRows (1623 : Fin 2425) =
    MixedData.row1623 := by decide +kernel

theorem sourceRowsAt1624 : MixedData.sourceRows (1624 : Fin 2425) =
    MixedData.row1624 := by decide +kernel

theorem sourceRowsAt1625 : MixedData.sourceRows (1625 : Fin 2425) =
    MixedData.row1625 := by decide +kernel

theorem sourceRowsAt1626 : MixedData.sourceRows (1626 : Fin 2425) =
    MixedData.row1626 := by decide +kernel

theorem sourceRowsAt1627 : MixedData.sourceRows (1627 : Fin 2425) =
    MixedData.row1627 := by decide +kernel

theorem sourceRowsAt1628 : MixedData.sourceRows (1628 : Fin 2425) =
    MixedData.row1628 := by decide +kernel

theorem sourceRowsAt1629 : MixedData.sourceRows (1629 : Fin 2425) =
    MixedData.row1629 := by decide +kernel

theorem sourceRowsAt1630 : MixedData.sourceRows (1630 : Fin 2425) =
    MixedData.row1630 := by decide +kernel

theorem sourceRowsAt1631 : MixedData.sourceRows (1631 : Fin 2425) =
    MixedData.row1631 := by decide +kernel

theorem chunkSound101_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 101) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1616 ∨ k.val = 1617 ∨ k.val = 1618 ∨ k.val = 1619 ∨ k.val = 1620 ∨ k.val = 1621 ∨ k.val = 1622 ∨ k.val = 1623 ∨ k.val = 1624 ∨ k.val = 1625 ∨ k.val = 1626 ∨ k.val = 1627 ∨ k.val = 1628 ∨ k.val = 1629 ∨ k.val = 1630 ∨ k.val = 1631 := by omega
  rcases heq with h1616 | h1617 | h1618 | h1619 | h1620 | h1621 | h1622 | h1623 | h1624 | h1625 | h1626 | h1627 | h1628 | h1629 | h1630 | h1631
  · have he : k = (1616 : Fin 2425) := Fin.ext h1616
    subst k
    rw [sourceRowsAt1616]
    exact rowSound1616 B hB hF
  · have he : k = (1617 : Fin 2425) := Fin.ext h1617
    subst k
    rw [sourceRowsAt1617]
    exact rowSound1617 B hB hF
  · have he : k = (1618 : Fin 2425) := Fin.ext h1618
    subst k
    rw [sourceRowsAt1618]
    exact rowSound1618 B hB hF
  · have he : k = (1619 : Fin 2425) := Fin.ext h1619
    subst k
    rw [sourceRowsAt1619]
    exact rowSound1619 B hB hF
  · have he : k = (1620 : Fin 2425) := Fin.ext h1620
    subst k
    rw [sourceRowsAt1620]
    exact rowSound1620 B hB hF
  · have he : k = (1621 : Fin 2425) := Fin.ext h1621
    subst k
    rw [sourceRowsAt1621]
    exact rowSound1621 B hB hF
  · have he : k = (1622 : Fin 2425) := Fin.ext h1622
    subst k
    rw [sourceRowsAt1622]
    exact rowSound1622 B hB hF
  · have he : k = (1623 : Fin 2425) := Fin.ext h1623
    subst k
    rw [sourceRowsAt1623]
    exact rowSound1623 B hB hF
  · have he : k = (1624 : Fin 2425) := Fin.ext h1624
    subst k
    rw [sourceRowsAt1624]
    exact rowSound1624 B hB hF
  · have he : k = (1625 : Fin 2425) := Fin.ext h1625
    subst k
    rw [sourceRowsAt1625]
    exact rowSound1625 B hB hF
  · have he : k = (1626 : Fin 2425) := Fin.ext h1626
    subst k
    rw [sourceRowsAt1626]
    exact rowSound1626 B hB hF
  · have he : k = (1627 : Fin 2425) := Fin.ext h1627
    subst k
    rw [sourceRowsAt1627]
    exact rowSound1627 B hB hF
  · have he : k = (1628 : Fin 2425) := Fin.ext h1628
    subst k
    rw [sourceRowsAt1628]
    exact rowSound1628 B hB hF
  · have he : k = (1629 : Fin 2425) := Fin.ext h1629
    subst k
    rw [sourceRowsAt1629]
    exact rowSound1629 B hB hF
  · have he : k = (1630 : Fin 2425) := Fin.ext h1630
    subst k
    rw [sourceRowsAt1630]
    exact rowSound1630 B hB hF
  · have he : k = (1631 : Fin 2425) := Fin.ext h1631
    subst k
    rw [sourceRowsAt1631]
    exact rowSound1631 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e_oai
