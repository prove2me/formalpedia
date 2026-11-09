-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:30:22.423515+00:00
-- url     : https://prove2.me/submissions/c7c95945-9c8e-4c7b-8794-187b175ccd62

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E119
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19487 raw19487Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw19487 raw19487Labels = mixedMoment B raw19487step0 raw19487step0Labels := by
      have hz : ∀ j, raw19487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19487step0 = (fun i j => raw19487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19487step0 raw19487; decide +kernel
      have hl : raw19487step0Labels = raw19487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487 raw19487Labels permutation434 hz
    mixedMoment B raw19487step0 raw19487step0Labels = mixedMoment B raw19487step1 raw19487step1Labels := by
      have hz : ∀ j, raw19487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19487step1 = (fun i j => raw19487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19487step1 raw19487step0; decide +kernel
      have hl : raw19487step1Labels = raw19487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487step0 raw19487step0Labels permutation80 hz
    mixedMoment B raw19487step1 raw19487step1Labels = mixedMoment B raw19487step2 raw19487step2Labels := by
      have ha : raw19487step2 = (fun i j => raw19487step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19487step2 raw19487step1; decide +kernel
      have hl : raw19487step2Labels = raw19487step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19487step1 raw19487step1Labels permutation29 permutation2
    mixedMoment B raw19487step2 raw19487step2Labels = mixedMoment B raw19487step3 raw19487step3Labels := by
      have ha : raw19487step3 = -raw19487step2 := by apply Matrix.ext; change ∀ i j, raw19487step3 i j = -(raw19487step2 i j); unfold raw19487step3 raw19487step2; decide +kernel
      have hl : raw19487step3Labels = raw19487step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical19488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19488 raw19488Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw19488 raw19488Labels = mixedMoment B raw19488step0 raw19488step0Labels := by
      have hz : ∀ j, raw19488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19488step0 = (fun i j => raw19488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19488step0 raw19488; decide +kernel
      have hl : raw19488step0Labels = raw19488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488 raw19488Labels permutation434 hz
    mixedMoment B raw19488step0 raw19488step0Labels = mixedMoment B raw19488step1 raw19488step1Labels := by
      have hz : ∀ j, raw19488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19488step1 = (fun i j => raw19488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19488step1 raw19488step0; decide +kernel
      have hl : raw19488step1Labels = raw19488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488step0 raw19488step0Labels permutation80 hz
    mixedMoment B raw19488step1 raw19488step1Labels = mixedMoment B raw19488step2 raw19488step2Labels := by
      have ha : raw19488step2 = (fun i j => raw19488step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19488step2 raw19488step1; decide +kernel
      have hl : raw19488step2Labels = raw19488step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19488step1 raw19488step1Labels permutation28 permutation0
    mixedMoment B raw19488step2 raw19488step2Labels = mixedMoment B raw19488step3 raw19488step3Labels := by
      have ha : raw19488step3 = -raw19488step2 := by apply Matrix.ext; change ∀ i j, raw19488step3 i j = -(raw19488step2 i j); unfold raw19488step3 raw19488step2; decide +kernel
      have hl : raw19488step3Labels = raw19488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical19492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19492 raw19492Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw19492 raw19492Labels = mixedMoment B raw19492step0 raw19492step0Labels := by
      have hz : ∀ j, raw19492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19492step0 = (fun i j => raw19492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19492step0 raw19492; decide +kernel
      have hl : raw19492step0Labels = raw19492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492 raw19492Labels permutation434 hz
    mixedMoment B raw19492step0 raw19492step0Labels = mixedMoment B raw19492step1 raw19492step1Labels := by
      have hz : ∀ j, raw19492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19492step1 = (fun i j => raw19492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19492step1 raw19492step0; decide +kernel
      have hl : raw19492step1Labels = raw19492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492step0 raw19492step0Labels permutation80 hz
    _ = mixedMoment B node1258 node1258Labels := by rfl

theorem canonical19498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19498 raw19498Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw19498 raw19498Labels = mixedMoment B raw19498step0 raw19498step0Labels := by
      have hz : ∀ j, raw19498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19498step0 = (fun i j => raw19498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19498step0 raw19498; decide +kernel
      have hl : raw19498step0Labels = raw19498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19498 raw19498Labels permutation346 hz
    mixedMoment B raw19498step0 raw19498step0Labels = mixedMoment B raw19498step1 raw19498step1Labels := by
      have ha : raw19498step1 = (fun i j => raw19498step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19498step1 raw19498step0; decide +kernel
      have hl : raw19498step1Labels = raw19498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19498step0 raw19498step0Labels permutation137 permutation2
    mixedMoment B raw19498step1 raw19498step1Labels = mixedMoment B raw19498step2 raw19498step2Labels := by
      have ha : raw19498step2 = -raw19498step1 := by apply Matrix.ext; change ∀ i j, raw19498step2 i j = -(raw19498step1 i j); unfold raw19498step2 raw19498step1; decide +kernel
      have hl : raw19498step2Labels = raw19498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical19499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19499 raw19499Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw19499 raw19499Labels = mixedMoment B raw19499step0 raw19499step0Labels := by
      have hz : ∀ j, raw19499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19499step0 = (fun i j => raw19499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19499step0 raw19499; decide +kernel
      have hl : raw19499step0Labels = raw19499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19499 raw19499Labels permutation346 hz
    mixedMoment B raw19499step0 raw19499step0Labels = mixedMoment B raw19499step1 raw19499step1Labels := by
      have ha : raw19499step1 = (fun i j => raw19499step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19499step1 raw19499step0; decide +kernel
      have hl : raw19499step1Labels = raw19499step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19499step0 raw19499step0Labels permutation137 permutation0
    mixedMoment B raw19499step1 raw19499step1Labels = mixedMoment B raw19499step2 raw19499step2Labels := by
      have ha : raw19499step2 = -raw19499step1 := by apply Matrix.ext; change ∀ i j, raw19499step2 i j = -(raw19499step1 i j); unfold raw19499step2 raw19499step1; decide +kernel
      have hl : raw19499step2Labels = raw19499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical19503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19503 raw19503Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw19503 raw19503Labels = mixedMoment B raw19503step0 raw19503step0Labels := by
      have hz : ∀ j, raw19503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19503step0 = (fun i j => raw19503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19503step0 raw19503; decide +kernel
      have hl : raw19503step0Labels = raw19503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19503 raw19503Labels permutation346 hz
    mixedMoment B raw19503step0 raw19503step0Labels = mixedMoment B raw19503step1 raw19503step1Labels := by
      have ha : raw19503step1 = (fun i j => raw19503step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19503step1 raw19503step0; decide +kernel
      have hl : raw19503step1Labels = raw19503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19503step0 raw19503step0Labels permutation38 permutation2
    _ = mixedMoment B node1211 node1211Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20097 raw20097Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20097 raw20097Labels = mixedMoment B raw20097step0 raw20097step0Labels := by
      have hz : ∀ j, raw20097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20097step0 = (fun i j => raw20097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20097step0 raw20097; decide +kernel
      have hl : raw20097step0Labels = raw20097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097 raw20097Labels permutation434 hz
    mixedMoment B raw20097step0 raw20097step0Labels = mixedMoment B raw20097step1 raw20097step1Labels := by
      have hz : ∀ j, raw20097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20097step1 = (fun i j => raw20097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20097step1 raw20097step0; decide +kernel
      have hl : raw20097step1Labels = raw20097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step0 raw20097step0Labels permutation80 hz
    mixedMoment B raw20097step1 raw20097step1Labels = mixedMoment B raw20097step2 raw20097step2Labels := by
      have hz : ∀ j, raw20097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20097step2 = (fun i j => raw20097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20097step2 raw20097step1; decide +kernel
      have hl : raw20097step2Labels = raw20097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step1 raw20097step1Labels permutation14 hz
    mixedMoment B raw20097step2 raw20097step2Labels = mixedMoment B raw20097step3 raw20097step3Labels := by
      have ha : raw20097step3 = (fun i j => raw20097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20097step3 raw20097step2; decide +kernel
      have hl : raw20097step3Labels = raw20097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20097step2 raw20097step2Labels permutation7 permutation2
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical20103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20103 raw20103Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw20103 raw20103Labels = mixedMoment B raw20103step0 raw20103step0Labels := by
      have hz : ∀ j, raw20103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20103step0 = (fun i j => raw20103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20103step0 raw20103; decide +kernel
      have hl : raw20103step0Labels = raw20103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103 raw20103Labels permutation434 hz
    mixedMoment B raw20103step0 raw20103step0Labels = mixedMoment B raw20103step1 raw20103step1Labels := by
      have hz : ∀ j, raw20103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20103step1 = (fun i j => raw20103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20103step1 raw20103step0; decide +kernel
      have hl : raw20103step1Labels = raw20103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step0 raw20103step0Labels permutation80 hz
    mixedMoment B raw20103step1 raw20103step1Labels = mixedMoment B raw20103step2 raw20103step2Labels := by
      have hz : ∀ j, raw20103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20103step2 = (fun i j => raw20103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20103step2 raw20103step1; decide +kernel
      have hl : raw20103step2Labels = raw20103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step1 raw20103step1Labels permutation14 hz
    mixedMoment B raw20103step2 raw20103step2Labels = mixedMoment B raw20103step3 raw20103step3Labels := by
      have ha : raw20103step3 = (fun i j => raw20103step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20103step3 raw20103step2; decide +kernel
      have hl : raw20103step3Labels = raw20103step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20103step2 raw20103step2Labels permutation3 permutation4
    mixedMoment B raw20103step3 raw20103step3Labels = mixedMoment B raw20103step4 raw20103step4Labels := by
      have ha : raw20103step4 = -raw20103step3 := by apply Matrix.ext; change ∀ i j, raw20103step4 i j = -(raw20103step3 i j); unfold raw20103step4 raw20103step3; decide +kernel
      have hl : raw20103step4Labels = raw20103step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical20105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20105 raw20105Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20105 raw20105Labels = mixedMoment B raw20105step0 raw20105step0Labels := by
      have hz : ∀ j, raw20105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20105step0 = (fun i j => raw20105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20105step0 raw20105; decide +kernel
      have hl : raw20105step0Labels = raw20105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105 raw20105Labels permutation434 hz
    mixedMoment B raw20105step0 raw20105step0Labels = mixedMoment B raw20105step1 raw20105step1Labels := by
      have hz : ∀ j, raw20105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20105step1 = (fun i j => raw20105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20105step1 raw20105step0; decide +kernel
      have hl : raw20105step1Labels = raw20105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105step0 raw20105step0Labels permutation80 hz
    mixedMoment B raw20105step1 raw20105step1Labels = mixedMoment B raw20105step2 raw20105step2Labels := by
      have ha : raw20105step2 = (fun i j => raw20105step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20105step2 raw20105step1; decide +kernel
      have hl : raw20105step2Labels = raw20105step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20105step1 raw20105step1Labels permutation9 permutation4
    mixedMoment B raw20105step2 raw20105step2Labels = mixedMoment B raw20105step3 raw20105step3Labels := by
      have ha : raw20105step3 = -raw20105step2 := by apply Matrix.ext; change ∀ i j, raw20105step3 i j = -(raw20105step2 i j); unfold raw20105step3 raw20105step2; decide +kernel
      have hl : raw20105step3Labels = raw20105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

theorem canonical20134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20134 raw20134Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20134 raw20134Labels = mixedMoment B raw20134step0 raw20134step0Labels := by
      have hz : ∀ j, raw20134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20134step0 = (fun i j => raw20134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20134step0 raw20134; decide +kernel
      have hl : raw20134step0Labels = raw20134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20134 raw20134Labels permutation346 hz
    mixedMoment B raw20134step0 raw20134step0Labels = mixedMoment B raw20134step1 raw20134step1Labels := by
      have ha : raw20134step1 = (fun i j => raw20134step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20134step1 raw20134step0; decide +kernel
      have hl : raw20134step1Labels = raw20134step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20134step0 raw20134step0Labels permutation33 permutation4
    mixedMoment B raw20134step1 raw20134step1Labels = mixedMoment B raw20134step2 raw20134step2Labels := by
      have ha : raw20134step2 = -raw20134step1 := by apply Matrix.ext; change ∀ i j, raw20134step2 i j = -(raw20134step1 i j); unfold raw20134step2 raw20134step1; decide +kernel
      have hl : raw20134step2Labels = raw20134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

theorem canonical20161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20161 raw20161Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20161 raw20161Labels = mixedMoment B raw20161step0 raw20161step0Labels := by
      have hz : ∀ j, raw20161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20161step0 = (fun i j => raw20161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20161step0 raw20161; decide +kernel
      have hl : raw20161step0Labels = raw20161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161 raw20161Labels permutation346 hz
    mixedMoment B raw20161step0 raw20161step0Labels = mixedMoment B raw20161step1 raw20161step1Labels := by
      have hz : ∀ j, raw20161step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20161step1 = (fun i j => raw20161step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20161step1 raw20161step0; decide +kernel
      have hl : raw20161step1Labels = raw20161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161step0 raw20161step0Labels permutation56 hz
    mixedMoment B raw20161step1 raw20161step1Labels = mixedMoment B raw20161step2 raw20161step2Labels := by
      have ha : raw20161step2 = (fun i j => raw20161step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20161step2 raw20161step1; decide +kernel
      have hl : raw20161step2Labels = raw20161step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20161step1 raw20161step1Labels permutation10 permutation4
    mixedMoment B raw20161step2 raw20161step2Labels = mixedMoment B raw20161step3 raw20161step3Labels := by
      have ha : raw20161step3 = -raw20161step2 := by apply Matrix.ext; change ∀ i j, raw20161step3 i j = -(raw20161step2 i j); unfold raw20161step3 raw20161step2; decide +kernel
      have hl : raw20161step3Labels = raw20161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20164 raw20164Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw20164 raw20164Labels = mixedMoment B raw20164step0 raw20164step0Labels := by
      have hz : ∀ j, raw20164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20164step0 = (fun i j => raw20164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20164step0 raw20164; decide +kernel
      have hl : raw20164step0Labels = raw20164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20164 raw20164Labels permutation346 hz
    mixedMoment B raw20164step0 raw20164step0Labels = mixedMoment B raw20164step1 raw20164step1Labels := by
      have ha : raw20164step1 = (fun i j => raw20164step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20164step1 raw20164step0; decide +kernel
      have hl : raw20164step1Labels = raw20164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20164step0 raw20164step0Labels permutation34 permutation4
    mixedMoment B raw20164step1 raw20164step1Labels = mixedMoment B raw20164step2 raw20164step2Labels := by
      have ha : raw20164step2 = -raw20164step1 := by apply Matrix.ext; change ∀ i j, raw20164step2 i j = -(raw20164step1 i j); unfold raw20164step2 raw20164step1; decide +kernel
      have hl : raw20164step2Labels = raw20164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1604 node1604Labels := by rfl

theorem canonical20212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20212 raw20212Labels = mixedMoment B node1596 node1596Labels := by
  calc
    mixedMoment B raw20212 raw20212Labels = mixedMoment B raw20212step0 raw20212step0Labels := by
      have ha : raw20212step0 = (fun i j => raw20212 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20212step0 raw20212; decide +kernel
      have hl : raw20212step0Labels = raw20212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20212 raw20212Labels permutation164 permutation4
    mixedMoment B raw20212step0 raw20212step0Labels = mixedMoment B raw20212step1 raw20212step1Labels := by
      have ha : raw20212step1 = -raw20212step0 := by apply Matrix.ext; change ∀ i j, raw20212step1 i j = -(raw20212step0 i j); unfold raw20212step1 raw20212step0; decide +kernel
      have hl : raw20212step1Labels = raw20212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1596 node1596Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20255 raw20255Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20255 raw20255Labels = mixedMoment B raw20255step0 raw20255step0Labels := by
      have hz : ∀ j, raw20255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20255step0 = (fun i j => raw20255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20255step0 raw20255; decide +kernel
      have hl : raw20255step0Labels = raw20255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255 raw20255Labels permutation434 hz
    mixedMoment B raw20255step0 raw20255step0Labels = mixedMoment B raw20255step1 raw20255step1Labels := by
      have hz : ∀ j, raw20255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20255step1 = (fun i j => raw20255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20255step1 raw20255step0; decide +kernel
      have hl : raw20255step1Labels = raw20255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255step0 raw20255step0Labels permutation80 hz
    mixedMoment B raw20255step1 raw20255step1Labels = mixedMoment B raw20255step2 raw20255step2Labels := by
      have ha : raw20255step2 = (fun i j => raw20255step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20255step2 raw20255step1; decide +kernel
      have hl : raw20255step2Labels = raw20255step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20255step1 raw20255step1Labels permutation9 permutation4
    mixedMoment B raw20255step2 raw20255step2Labels = mixedMoment B raw20255step3 raw20255step3Labels := by
      have ha : raw20255step3 = -raw20255step2 := by apply Matrix.ext; change ∀ i j, raw20255step3 i j = -(raw20255step2 i j); unfold raw20255step3 raw20255step2; decide +kernel
      have hl : raw20255step3Labels = raw20255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical20259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20259 raw20259Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20259 raw20259Labels = mixedMoment B raw20259step0 raw20259step0Labels := by
      have hz : ∀ j, raw20259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20259step0 = (fun i j => raw20259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20259step0 raw20259; decide +kernel
      have hl : raw20259step0Labels = raw20259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259 raw20259Labels permutation434 hz
    mixedMoment B raw20259step0 raw20259step0Labels = mixedMoment B raw20259step1 raw20259step1Labels := by
      have hz : ∀ j, raw20259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20259step1 = (fun i j => raw20259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20259step1 raw20259step0; decide +kernel
      have hl : raw20259step1Labels = raw20259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259step0 raw20259step0Labels permutation80 hz
    mixedMoment B raw20259step1 raw20259step1Labels = mixedMoment B raw20259step2 raw20259step2Labels := by
      have ha : raw20259step2 = (fun i j => raw20259step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20259step2 raw20259step1; decide +kernel
      have hl : raw20259step2Labels = raw20259step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20259step1 raw20259step1Labels permutation10 permutation2
    mixedMoment B raw20259step2 raw20259step2Labels = mixedMoment B raw20259step3 raw20259step3Labels := by
      have ha : raw20259step3 = -raw20259step2 := by apply Matrix.ext; change ∀ i j, raw20259step3 i j = -(raw20259step2 i j); unfold raw20259step3 raw20259step2; decide +kernel
      have hl : raw20259step3Labels = raw20259step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20261 raw20261Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20261 raw20261Labels = mixedMoment B raw20261step0 raw20261step0Labels := by
      have hz : ∀ j, raw20261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20261step0 = (fun i j => raw20261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20261step0 raw20261; decide +kernel
      have hl : raw20261step0Labels = raw20261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20261 raw20261Labels permutation434 hz
    mixedMoment B raw20261step0 raw20261step0Labels = mixedMoment B raw20261step1 raw20261step1Labels := by
      have ha : raw20261step1 = (fun i j => raw20261step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20261step1 raw20261step0; decide +kernel
      have hl : raw20261step1Labels = raw20261step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20261step0 raw20261step0Labels permutation33 permutation4
    mixedMoment B raw20261step1 raw20261step1Labels = mixedMoment B raw20261step2 raw20261step2Labels := by
      have ha : raw20261step2 = -raw20261step1 := by apply Matrix.ext; change ∀ i j, raw20261step2 i j = -(raw20261step1 i j); unfold raw20261step2 raw20261step1; decide +kernel
      have hl : raw20261step2Labels = raw20261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

theorem canonical20262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20262 raw20262Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw20262 raw20262Labels = mixedMoment B raw20262step0 raw20262step0Labels := by
      have hz : ∀ j, raw20262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20262step0 = (fun i j => raw20262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20262step0 raw20262; decide +kernel
      have hl : raw20262step0Labels = raw20262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20262 raw20262Labels permutation434 hz
    mixedMoment B raw20262step0 raw20262step0Labels = mixedMoment B raw20262step1 raw20262step1Labels := by
      have hz : ∀ j, raw20262step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20262step1 = (fun i j => raw20262step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20262step1 raw20262step0; decide +kernel
      have hl : raw20262step1Labels = raw20262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20262step0 raw20262step0Labels permutation80 hz
    mixedMoment B raw20262step1 raw20262step1Labels = mixedMoment B raw20262step2 raw20262step2Labels := by
      have ha : raw20262step2 = (fun i j => raw20262step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20262step2 raw20262step1; decide +kernel
      have hl : raw20262step2Labels = raw20262step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20262step1 raw20262step1Labels permutation8 permutation4
    mixedMoment B raw20262step2 raw20262step2Labels = mixedMoment B raw20262step3 raw20262step3Labels := by
      have ha : raw20262step3 = -raw20262step2 := by apply Matrix.ext; change ∀ i j, raw20262step3 i j = -(raw20262step2 i j); unfold raw20262step3 raw20262step2; decide +kernel
      have hl : raw20262step3Labels = raw20262step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1630 node1630Labels := by rfl

theorem canonical20263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20263 raw20263Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20263 raw20263Labels = mixedMoment B raw20263step0 raw20263step0Labels := by
      have hz : ∀ j, raw20263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20263step0 = (fun i j => raw20263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20263step0 raw20263; decide +kernel
      have hl : raw20263step0Labels = raw20263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20263 raw20263Labels permutation434 hz
    mixedMoment B raw20263step0 raw20263step0Labels = mixedMoment B raw20263step1 raw20263step1Labels := by
      have hz : ∀ j, raw20263step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20263step1 = (fun i j => raw20263step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20263step1 raw20263step0; decide +kernel
      have hl : raw20263step1Labels = raw20263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20263step0 raw20263step0Labels permutation56 hz
    mixedMoment B raw20263step1 raw20263step1Labels = mixedMoment B raw20263step2 raw20263step2Labels := by
      have ha : raw20263step2 = (fun i j => raw20263step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20263step2 raw20263step1; decide +kernel
      have hl : raw20263step2Labels = raw20263step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20263step1 raw20263step1Labels permutation9 permutation4
    mixedMoment B raw20263step2 raw20263step2Labels = mixedMoment B raw20263step3 raw20263step3Labels := by
      have ha : raw20263step3 = -raw20263step2 := by apply Matrix.ext; change ∀ i j, raw20263step3 i j = -(raw20263step2 i j); unfold raw20263step3 raw20263step2; decide +kernel
      have hl : raw20263step3Labels = raw20263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical20264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20264 raw20264Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20264 raw20264Labels = mixedMoment B raw20264step0 raw20264step0Labels := by
      have hz : ∀ j, raw20264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20264step0 = (fun i j => raw20264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20264step0 raw20264; decide +kernel
      have hl : raw20264step0Labels = raw20264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20264 raw20264Labels permutation346 hz
    mixedMoment B raw20264step0 raw20264step0Labels = mixedMoment B raw20264step1 raw20264step1Labels := by
      have hz : ∀ j, raw20264step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20264step1 = (fun i j => raw20264step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20264step1 raw20264step0; decide +kernel
      have hl : raw20264step1Labels = raw20264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20264step0 raw20264step0Labels permutation56 hz
    mixedMoment B raw20264step1 raw20264step1Labels = mixedMoment B raw20264step2 raw20264step2Labels := by
      have ha : raw20264step2 = (fun i j => raw20264step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20264step2 raw20264step1; decide +kernel
      have hl : raw20264step2Labels = raw20264step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20264step1 raw20264step1Labels permutation9 permutation4
    mixedMoment B raw20264step2 raw20264step2Labels = mixedMoment B raw20264step3 raw20264step3Labels := by
      have ha : raw20264step3 = -raw20264step2 := by apply Matrix.ext; change ∀ i j, raw20264step3 i j = -(raw20264step2 i j); unfold raw20264step3 raw20264step2; decide +kernel
      have hl : raw20264step3Labels = raw20264step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical20265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20265 raw20265Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20265 raw20265Labels = mixedMoment B raw20265step0 raw20265step0Labels := by
      have hz : ∀ j, raw20265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20265step0 = (fun i j => raw20265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20265step0 raw20265; decide +kernel
      have hl : raw20265step0Labels = raw20265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265 raw20265Labels permutation434 hz
    mixedMoment B raw20265step0 raw20265step0Labels = mixedMoment B raw20265step1 raw20265step1Labels := by
      have hz : ∀ j, raw20265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20265step1 = (fun i j => raw20265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20265step1 raw20265step0; decide +kernel
      have hl : raw20265step1Labels = raw20265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step0 raw20265step0Labels permutation80 hz
    mixedMoment B raw20265step1 raw20265step1Labels = mixedMoment B raw20265step2 raw20265step2Labels := by
      have hz : ∀ j, raw20265step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20265step2 = (fun i j => raw20265step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20265step2 raw20265step1; decide +kernel
      have hl : raw20265step2Labels = raw20265step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step1 raw20265step1Labels permutation14 hz
    mixedMoment B raw20265step2 raw20265step2Labels = mixedMoment B raw20265step3 raw20265step3Labels := by
      have ha : raw20265step3 = -raw20265step2 := by apply Matrix.ext; change ∀ i j, raw20265step3 i j = -(raw20265step2 i j); unfold raw20265step3 raw20265step2; decide +kernel
      have hl : raw20265step3Labels = raw20265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

theorem canonical20266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20266 raw20266Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20266 raw20266Labels = mixedMoment B raw20266step0 raw20266step0Labels := by
      have hz : ∀ j, raw20266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20266step0 = (fun i j => raw20266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20266step0 raw20266; decide +kernel
      have hl : raw20266step0Labels = raw20266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20266 raw20266Labels permutation434 hz
    mixedMoment B raw20266step0 raw20266step0Labels = mixedMoment B raw20266step1 raw20266step1Labels := by
      have ha : raw20266step1 = (fun i j => raw20266step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20266step1 raw20266step0; decide +kernel
      have hl : raw20266step1Labels = raw20266step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20266step0 raw20266step0Labels permutation40 permutation2
    mixedMoment B raw20266step1 raw20266step1Labels = mixedMoment B raw20266step2 raw20266step2Labels := by
      have ha : raw20266step2 = -raw20266step1 := by apply Matrix.ext; change ∀ i j, raw20266step2 i j = -(raw20266step1 i j); unfold raw20266step2 raw20266step1; decide +kernel
      have hl : raw20266step2Labels = raw20266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20267 raw20267Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20267 raw20267Labels = mixedMoment B raw20267step0 raw20267step0Labels := by
      have hz : ∀ j, raw20267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20267step0 = (fun i j => raw20267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20267step0 raw20267; decide +kernel
      have hl : raw20267step0Labels = raw20267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20267 raw20267Labels permutation346 hz
    mixedMoment B raw20267step0 raw20267step0Labels = mixedMoment B raw20267step1 raw20267step1Labels := by
      have ha : raw20267step1 = (fun i j => raw20267step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20267step1 raw20267step0; decide +kernel
      have hl : raw20267step1Labels = raw20267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20267step0 raw20267step0Labels permutation40 permutation2
    mixedMoment B raw20267step1 raw20267step1Labels = mixedMoment B raw20267step2 raw20267step2Labels := by
      have ha : raw20267step2 = -raw20267step1 := by apply Matrix.ext; change ∀ i j, raw20267step2 i j = -(raw20267step1 i j); unfold raw20267step2 raw20267step1; decide +kernel
      have hl : raw20267step2Labels = raw20267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20268 raw20268Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20268 raw20268Labels = mixedMoment B raw20268step0 raw20268step0Labels := by
      have hz : ∀ j, raw20268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20268step0 = (fun i j => raw20268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20268step0 raw20268; decide +kernel
      have hl : raw20268step0Labels = raw20268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268 raw20268Labels permutation434 hz
    mixedMoment B raw20268step0 raw20268step0Labels = mixedMoment B raw20268step1 raw20268step1Labels := by
      have hz : ∀ j, raw20268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20268step1 = (fun i j => raw20268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20268step1 raw20268step0; decide +kernel
      have hl : raw20268step1Labels = raw20268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268step0 raw20268step0Labels permutation80 hz
    mixedMoment B raw20268step1 raw20268step1Labels = mixedMoment B raw20268step2 raw20268step2Labels := by
      have ha : raw20268step2 = (fun i j => raw20268step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20268step2 raw20268step1; decide +kernel
      have hl : raw20268step2Labels = raw20268step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20268step1 raw20268step1Labels permutation8 permutation4
    mixedMoment B raw20268step2 raw20268step2Labels = mixedMoment B raw20268step3 raw20268step3Labels := by
      have ha : raw20268step3 = -raw20268step2 := by apply Matrix.ext; change ∀ i j, raw20268step3 i j = -(raw20268step2 i j); unfold raw20268step3 raw20268step2; decide +kernel
      have hl : raw20268step3Labels = raw20268step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20269 raw20269Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw20269 raw20269Labels = mixedMoment B raw20269step0 raw20269step0Labels := by
      have hz : ∀ j, raw20269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20269step0 = (fun i j => raw20269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20269step0 raw20269; decide +kernel
      have hl : raw20269step0Labels = raw20269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20269 raw20269Labels permutation434 hz
    mixedMoment B raw20269step0 raw20269step0Labels = mixedMoment B raw20269step1 raw20269step1Labels := by
      have hz : ∀ j, raw20269step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20269step1 = (fun i j => raw20269step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20269step1 raw20269step0; decide +kernel
      have hl : raw20269step1Labels = raw20269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20269step0 raw20269step0Labels permutation80 hz
    mixedMoment B raw20269step1 raw20269step1Labels = mixedMoment B raw20269step2 raw20269step2Labels := by
      have ha : raw20269step2 = (fun i j => raw20269step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20269step2 raw20269step1; decide +kernel
      have hl : raw20269step2Labels = raw20269step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20269step1 raw20269step1Labels permutation8 permutation4
    mixedMoment B raw20269step2 raw20269step2Labels = mixedMoment B raw20269step3 raw20269step3Labels := by
      have ha : raw20269step3 = -raw20269step2 := by apply Matrix.ext; change ∀ i j, raw20269step3 i j = -(raw20269step2 i j); unfold raw20269step3 raw20269step2; decide +kernel
      have hl : raw20269step3Labels = raw20269step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3247 node3247Labels := by rfl

theorem canonical20270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20270 raw20270Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20270 raw20270Labels = mixedMoment B raw20270step0 raw20270step0Labels := by
      have hz : ∀ j, raw20270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20270step0 = (fun i j => raw20270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20270step0 raw20270; decide +kernel
      have hl : raw20270step0Labels = raw20270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20270 raw20270Labels permutation434 hz
    mixedMoment B raw20270step0 raw20270step0Labels = mixedMoment B raw20270step1 raw20270step1Labels := by
      have ha : raw20270step1 = (fun i j => raw20270step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20270step1 raw20270step0; decide +kernel
      have hl : raw20270step1Labels = raw20270step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20270step0 raw20270step0Labels permutation32 permutation4
    mixedMoment B raw20270step1 raw20270step1Labels = mixedMoment B raw20270step2 raw20270step2Labels := by
      have ha : raw20270step2 = -raw20270step1 := by apply Matrix.ext; change ∀ i j, raw20270step2 i j = -(raw20270step1 i j); unfold raw20270step2 raw20270step1; decide +kernel
      have hl : raw20270step2Labels = raw20270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

theorem canonical20271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20271 raw20271Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20271 raw20271Labels = mixedMoment B raw20271step0 raw20271step0Labels := by
      have hz : ∀ j, raw20271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20271step0 = (fun i j => raw20271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20271step0 raw20271; decide +kernel
      have hl : raw20271step0Labels = raw20271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20271 raw20271Labels permutation346 hz
    mixedMoment B raw20271step0 raw20271step0Labels = mixedMoment B raw20271step1 raw20271step1Labels := by
      have ha : raw20271step1 = (fun i j => raw20271step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20271step1 raw20271step0; decide +kernel
      have hl : raw20271step1Labels = raw20271step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20271step0 raw20271step0Labels permutation32 permutation4
    mixedMoment B raw20271step1 raw20271step1Labels = mixedMoment B raw20271step2 raw20271step2Labels := by
      have ha : raw20271step2 = -raw20271step1 := by apply Matrix.ext; change ∀ i j, raw20271step2 i j = -(raw20271step1 i j); unfold raw20271step2 raw20271step1; decide +kernel
      have hl : raw20271step2Labels = raw20271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

theorem canonical20273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20273 raw20273Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw20273 raw20273Labels = mixedMoment B raw20273step0 raw20273step0Labels := by
      have hz : ∀ j, raw20273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20273step0 = (fun i j => raw20273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20273step0 raw20273; decide +kernel
      have hl : raw20273step0Labels = raw20273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273 raw20273Labels permutation434 hz
    mixedMoment B raw20273step0 raw20273step0Labels = mixedMoment B raw20273step1 raw20273step1Labels := by
      have hz : ∀ j, raw20273step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20273step1 = (fun i j => raw20273step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20273step1 raw20273step0; decide +kernel
      have hl : raw20273step1Labels = raw20273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273step0 raw20273step0Labels permutation80 hz
    mixedMoment B raw20273step1 raw20273step1Labels = mixedMoment B raw20273step2 raw20273step2Labels := by
      have ha : raw20273step2 = (fun i j => raw20273step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20273step2 raw20273step1; decide +kernel
      have hl : raw20273step2Labels = raw20273step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20273step1 raw20273step1Labels permutation31 permutation2
    mixedMoment B raw20273step2 raw20273step2Labels = mixedMoment B raw20273step3 raw20273step3Labels := by
      have ha : raw20273step3 = -raw20273step2 := by apply Matrix.ext; change ∀ i j, raw20273step3 i j = -(raw20273step2 i j); unfold raw20273step3 raw20273step2; decide +kernel
      have hl : raw20273step3Labels = raw20273step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2130 node2130Labels := by rfl

theorem canonical20274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20274 raw20274Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw20274 raw20274Labels = mixedMoment B raw20274step0 raw20274step0Labels := by
      have hz : ∀ j, raw20274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20274step0 = (fun i j => raw20274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20274step0 raw20274; decide +kernel
      have hl : raw20274step0Labels = raw20274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20274 raw20274Labels permutation434 hz
    mixedMoment B raw20274step0 raw20274step0Labels = mixedMoment B raw20274step1 raw20274step1Labels := by
      have ha : raw20274step1 = (fun i j => raw20274step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20274step1 raw20274step0; decide +kernel
      have hl : raw20274step1Labels = raw20274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20274step0 raw20274step0Labels permutation149 permutation2
    mixedMoment B raw20274step1 raw20274step1Labels = mixedMoment B raw20274step2 raw20274step2Labels := by
      have ha : raw20274step2 = -raw20274step1 := by apply Matrix.ext; change ∀ i j, raw20274step2 i j = -(raw20274step1 i j); unfold raw20274step2 raw20274step1; decide +kernel
      have hl : raw20274step2Labels = raw20274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

theorem canonical20275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20275 raw20275Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw20275 raw20275Labels = mixedMoment B raw20275step0 raw20275step0Labels := by
      have hz : ∀ j, raw20275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20275step0 = (fun i j => raw20275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20275step0 raw20275; decide +kernel
      have hl : raw20275step0Labels = raw20275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20275 raw20275Labels permutation346 hz
    mixedMoment B raw20275step0 raw20275step0Labels = mixedMoment B raw20275step1 raw20275step1Labels := by
      have ha : raw20275step1 = (fun i j => raw20275step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20275step1 raw20275step0; decide +kernel
      have hl : raw20275step1Labels = raw20275step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20275step0 raw20275step0Labels permutation149 permutation2
    mixedMoment B raw20275step1 raw20275step1Labels = mixedMoment B raw20275step2 raw20275step2Labels := by
      have ha : raw20275step2 = -raw20275step1 := by apply Matrix.ext; change ∀ i j, raw20275step2 i j = -(raw20275step1 i j); unfold raw20275step2 raw20275step1; decide +kernel
      have hl : raw20275step2Labels = raw20275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

theorem canonical20276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20276 raw20276Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw20276 raw20276Labels = mixedMoment B raw20276step0 raw20276step0Labels := by
      have hz : ∀ j, raw20276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20276step0 = (fun i j => raw20276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20276step0 raw20276; decide +kernel
      have hl : raw20276step0Labels = raw20276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20276 raw20276Labels permutation434 hz
    mixedMoment B raw20276step0 raw20276step0Labels = mixedMoment B raw20276step1 raw20276step1Labels := by
      have hz : ∀ j, raw20276step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20276step1 = (fun i j => raw20276step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20276step1 raw20276step0; decide +kernel
      have hl : raw20276step1Labels = raw20276step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20276step0 raw20276step0Labels permutation80 hz
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical20277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20277 raw20277Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw20277 raw20277Labels = mixedMoment B raw20277step0 raw20277step0Labels := by
      have hz : ∀ j, raw20277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20277step0 = (fun i j => raw20277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20277step0 raw20277; decide +kernel
      have hl : raw20277step0Labels = raw20277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20277 raw20277Labels permutation346 hz
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical20278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20278 raw20278Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw20278 raw20278Labels = mixedMoment B raw20278step0 raw20278step0Labels := by
      have hz : ∀ j, raw20278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20278step0 = (fun i j => raw20278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20278step0 raw20278; decide +kernel
      have hl : raw20278step0Labels = raw20278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20278 raw20278Labels permutation346 hz
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical20279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20279 raw20279Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw20279 raw20279Labels = mixedMoment B raw20279step0 raw20279step0Labels := by
      have ha : raw20279step0 = (fun i j => raw20279 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20279step0 raw20279; decide +kernel
      have hl : raw20279step0Labels = raw20279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20279 raw20279Labels permutation158 permutation2
    _ = mixedMoment B node1111 node1111Labels := by rfl

theorem canonical20280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20280 raw20280Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20280 raw20280Labels = mixedMoment B raw20280step0 raw20280step0Labels := by
      have hz : ∀ j, raw20280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20280step0 = (fun i j => raw20280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20280step0 raw20280; decide +kernel
      have hl : raw20280step0Labels = raw20280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20280 raw20280Labels permutation346 hz
    mixedMoment B raw20280step0 raw20280step0Labels = mixedMoment B raw20280step1 raw20280step1Labels := by
      have ha : raw20280step1 = (fun i j => raw20280step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20280step1 raw20280step0; decide +kernel
      have hl : raw20280step1Labels = raw20280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20280step0 raw20280step0Labels permutation34 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical20281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20281 raw20281Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw20281 raw20281Labels = mixedMoment B raw20281step0 raw20281step0Labels := by
      have hz : ∀ j, raw20281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20281step0 = (fun i j => raw20281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20281step0 raw20281; decide +kernel
      have hl : raw20281step0Labels = raw20281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20281 raw20281Labels permutation346 hz
    _ = mixedMoment B node1119 node1119Labels := by rfl

theorem canonical20282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20282 raw20282Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20282 raw20282Labels = mixedMoment B raw20282step0 raw20282step0Labels := by
      have hz : ∀ j, raw20282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20282step0 = (fun i j => raw20282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20282step0 raw20282; decide +kernel
      have hl : raw20282step0Labels = raw20282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20282 raw20282Labels permutation346 hz
    _ = mixedMoment B node1115 node1115Labels := by rfl

theorem canonical20283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20283 raw20283Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20283 raw20283Labels = mixedMoment B raw20283step0 raw20283step0Labels := by
      have hz : ∀ j, raw20283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20283step0 = (fun i j => raw20283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20283step0 raw20283; decide +kernel
      have hl : raw20283step0Labels = raw20283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283 raw20283Labels permutation520 hz
    mixedMoment B raw20283step0 raw20283step0Labels = mixedMoment B raw20283step1 raw20283step1Labels := by
      have hz : ∀ j, raw20283step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20283step1 = (fun i j => raw20283step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20283step1 raw20283step0; decide +kernel
      have hl : raw20283step1Labels = raw20283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283step0 raw20283step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical20284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20284 raw20284Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20284 raw20284Labels = mixedMoment B raw20284step0 raw20284step0Labels := by
      have hz : ∀ j, raw20284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20284step0 = (fun i j => raw20284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20284step0 raw20284; decide +kernel
      have hl : raw20284step0Labels = raw20284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20284 raw20284Labels permutation346 hz
    mixedMoment B raw20284step0 raw20284step0Labels = mixedMoment B raw20284step1 raw20284step1Labels := by
      have ha : raw20284step1 = (fun i j => raw20284step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20284step1 raw20284step0; decide +kernel
      have hl : raw20284step1Labels = raw20284step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20284step0 raw20284step0Labels permutation34 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

theorem canonical20285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20285 raw20285Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw20285 raw20285Labels = mixedMoment B raw20285step0 raw20285step0Labels := by
      have ha : raw20285step0 = (fun i j => raw20285 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20285step0 raw20285; decide +kernel
      have hl : raw20285step0Labels = raw20285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20285 raw20285Labels permutation178 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

theorem canonical20286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20286 raw20286Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20286 raw20286Labels = mixedMoment B raw20286step0 raw20286step0Labels := by
      have hz : ∀ j, raw20286 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20286step0 = (fun i j => raw20286 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20286step0 raw20286; decide +kernel
      have hl : raw20286step0Labels = raw20286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20286 raw20286Labels permutation520 hz
    mixedMoment B raw20286step0 raw20286step0Labels = mixedMoment B raw20286step1 raw20286step1Labels := by
      have hz : ∀ j, raw20286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20286step1 = (fun i j => raw20286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20286step1 raw20286step0; decide +kernel
      have hl : raw20286step1Labels = raw20286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20286step0 raw20286step0Labels permutation80 hz
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical20287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20287 raw20287Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw20287 raw20287Labels = mixedMoment B raw20287step0 raw20287step0Labels := by
      have hz : ∀ j, raw20287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20287step0 = (fun i j => raw20287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20287step0 raw20287; decide +kernel
      have hl : raw20287step0Labels = raw20287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20287 raw20287Labels permutation346 hz
    mixedMoment B raw20287step0 raw20287step0Labels = mixedMoment B raw20287step1 raw20287step1Labels := by
      have ha : raw20287step1 = (fun i j => raw20287step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20287step1 raw20287step0; decide +kernel
      have hl : raw20287step1Labels = raw20287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20287step0 raw20287step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical20288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20288 raw20288Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw20288 raw20288Labels = mixedMoment B raw20288step0 raw20288step0Labels := by
      have hz : ∀ j, raw20288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20288step0 = (fun i j => raw20288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20288step0 raw20288; decide +kernel
      have hl : raw20288step0Labels = raw20288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20288 raw20288Labels permutation346 hz
    mixedMoment B raw20288step0 raw20288step0Labels = mixedMoment B raw20288step1 raw20288step1Labels := by
      have ha : raw20288step1 = (fun i j => raw20288step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20288step1 raw20288step0; decide +kernel
      have hl : raw20288step1Labels = raw20288step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20288step0 raw20288step0Labels permutation38 permutation2
    _ = mixedMoment B node630 node630Labels := by rfl

theorem canonical20289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20289 raw20289Labels = mixedMoment B node1150 node1150Labels := by
  calc
    mixedMoment B raw20289 raw20289Labels = mixedMoment B raw20289step0 raw20289step0Labels := by
      have ha : raw20289step0 = (fun i j => raw20289 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20289step0 raw20289; decide +kernel
      have hl : raw20289step0Labels = raw20289Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20289 raw20289Labels permutation182 permutation2
    _ = mixedMoment B node1150 node1150Labels := by rfl

theorem canonical20290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20290 raw20290Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20290 raw20290Labels = mixedMoment B raw20290step0 raw20290step0Labels := by
      have hz : ∀ j, raw20290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20290step0 = (fun i j => raw20290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20290step0 raw20290; decide +kernel
      have hl : raw20290step0Labels = raw20290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20290 raw20290Labels permutation346 hz
    mixedMoment B raw20290step0 raw20290step0Labels = mixedMoment B raw20290step1 raw20290step1Labels := by
      have ha : raw20290step1 = (fun i j => raw20290step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20290step1 raw20290step0; decide +kernel
      have hl : raw20290step1Labels = raw20290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20290step0 raw20290step0Labels permutation38 permutation2
    _ = mixedMoment B node1136 node1136Labels := by rfl

theorem canonical20291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20291 raw20291Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20291 raw20291Labels = mixedMoment B raw20291step0 raw20291step0Labels := by
      have hz : ∀ j, raw20291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20291step0 = (fun i j => raw20291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20291step0 raw20291; decide +kernel
      have hl : raw20291step0Labels = raw20291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20291 raw20291Labels permutation346 hz
    mixedMoment B raw20291step0 raw20291step0Labels = mixedMoment B raw20291step1 raw20291step1Labels := by
      have ha : raw20291step1 = (fun i j => raw20291step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20291step1 raw20291step0; decide +kernel
      have hl : raw20291step1Labels = raw20291step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20291step0 raw20291step0Labels permutation40 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical20292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20292 raw20292Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw20292 raw20292Labels = mixedMoment B raw20292step0 raw20292step0Labels := by
      have ha : raw20292step0 = (fun i j => raw20292 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20292step0 raw20292; decide +kernel
      have hl : raw20292step0Labels = raw20292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20292 raw20292Labels permutation200 permutation2
    _ = mixedMoment B node1112 node1112Labels := by rfl

theorem canonical20293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20293 raw20293Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw20293 raw20293Labels = mixedMoment B raw20293step0 raw20293step0Labels := by
      have hz : ∀ j, raw20293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20293step0 = (fun i j => raw20293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20293step0 raw20293; decide +kernel
      have hl : raw20293step0Labels = raw20293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20293 raw20293Labels permutation346 hz
    mixedMoment B raw20293step0 raw20293step0Labels = mixedMoment B raw20293step1 raw20293step1Labels := by
      have ha : raw20293step1 = (fun i j => raw20293step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20293step1 raw20293step0; decide +kernel
      have hl : raw20293step1Labels = raw20293step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20293step0 raw20293step0Labels permutation38 permutation2
    _ = mixedMoment B node1120 node1120Labels := by rfl

theorem canonical20294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20294 raw20294Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20294 raw20294Labels = mixedMoment B raw20294step0 raw20294step0Labels := by
      have hz : ∀ j, raw20294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20294step0 = (fun i j => raw20294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20294step0 raw20294; decide +kernel
      have hl : raw20294step0Labels = raw20294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20294 raw20294Labels permutation346 hz
    mixedMoment B raw20294step0 raw20294step0Labels = mixedMoment B raw20294step1 raw20294step1Labels := by
      have ha : raw20294step1 = (fun i j => raw20294step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20294step1 raw20294step0; decide +kernel
      have hl : raw20294step1Labels = raw20294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20294step0 raw20294step0Labels permutation38 permutation2
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical20295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20295 raw20295Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20295 raw20295Labels = mixedMoment B raw20295step0 raw20295step0Labels := by
      have hz : ∀ j, raw20295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20295step0 = (fun i j => raw20295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20295step0 raw20295; decide +kernel
      have hl : raw20295step0Labels = raw20295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20295 raw20295Labels permutation346 hz
    mixedMoment B raw20295step0 raw20295step0Labels = mixedMoment B raw20295step1 raw20295step1Labels := by
      have ha : raw20295step1 = (fun i j => raw20295step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20295step1 raw20295step0; decide +kernel
      have hl : raw20295step1Labels = raw20295step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20295step0 raw20295step0Labels permutation34 permutation4
    mixedMoment B raw20295step1 raw20295step1Labels = mixedMoment B raw20295step2 raw20295step2Labels := by
      have ha : raw20295step2 = -raw20295step1 := by apply Matrix.ext; change ∀ i j, raw20295step2 i j = -(raw20295step1 i j); unfold raw20295step2 raw20295step1; decide +kernel
      have hl : raw20295step2Labels = raw20295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20296 raw20296Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20296 raw20296Labels = mixedMoment B raw20296step0 raw20296step0Labels := by
      have hz : ∀ j, raw20296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20296step0 = (fun i j => raw20296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20296step0 raw20296; decide +kernel
      have hl : raw20296step0Labels = raw20296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20296 raw20296Labels permutation346 hz
    mixedMoment B raw20296step0 raw20296step0Labels = mixedMoment B raw20296step1 raw20296step1Labels := by
      have ha : raw20296step1 = (fun i j => raw20296step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20296step1 raw20296step0; decide +kernel
      have hl : raw20296step1Labels = raw20296step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20296step0 raw20296step0Labels permutation41 permutation2
    mixedMoment B raw20296step1 raw20296step1Labels = mixedMoment B raw20296step2 raw20296step2Labels := by
      have ha : raw20296step2 = -raw20296step1 := by apply Matrix.ext; change ∀ i j, raw20296step2 i j = -(raw20296step1 i j); unfold raw20296step2 raw20296step1; decide +kernel
      have hl : raw20296step2Labels = raw20296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

theorem canonical20297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20297 raw20297Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw20297 raw20297Labels = mixedMoment B raw20297step0 raw20297step0Labels := by
      have ha : raw20297step0 = (fun i j => raw20297 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20297step0 raw20297; decide +kernel
      have hl : raw20297step0Labels = raw20297Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20297 raw20297Labels permutation200 permutation2
    mixedMoment B raw20297step0 raw20297step0Labels = mixedMoment B raw20297step1 raw20297step1Labels := by
      have ha : raw20297step1 = -raw20297step0 := by apply Matrix.ext; change ∀ i j, raw20297step1 i j = -(raw20297step0 i j); unfold raw20297step1 raw20297step0; decide +kernel
      have hl : raw20297step1Labels = raw20297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1613 node1613Labels := by rfl

theorem canonical20298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20298 raw20298Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20298 raw20298Labels = mixedMoment B raw20298step0 raw20298step0Labels := by
      have hz : ∀ j, raw20298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20298step0 = (fun i j => raw20298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20298step0 raw20298; decide +kernel
      have hl : raw20298step0Labels = raw20298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298 raw20298Labels permutation434 hz
    mixedMoment B raw20298step0 raw20298step0Labels = mixedMoment B raw20298step1 raw20298step1Labels := by
      have hz : ∀ j, raw20298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20298step1 = (fun i j => raw20298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20298step1 raw20298step0; decide +kernel
      have hl : raw20298step1Labels = raw20298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298step0 raw20298step0Labels permutation80 hz
    mixedMoment B raw20298step1 raw20298step1Labels = mixedMoment B raw20298step2 raw20298step2Labels := by
      have ha : raw20298step2 = -raw20298step1 := by apply Matrix.ext; change ∀ i j, raw20298step2 i j = -(raw20298step1 i j); unfold raw20298step2 raw20298step1; decide +kernel
      have hl : raw20298step2Labels = raw20298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20299 raw20299Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20299 raw20299Labels = mixedMoment B raw20299step0 raw20299step0Labels := by
      have hz : ∀ j, raw20299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20299step0 = (fun i j => raw20299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20299step0 raw20299; decide +kernel
      have hl : raw20299step0Labels = raw20299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20299 raw20299Labels permutation346 hz
    mixedMoment B raw20299step0 raw20299step0Labels = mixedMoment B raw20299step1 raw20299step1Labels := by
      have ha : raw20299step1 = (fun i j => raw20299step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20299step1 raw20299step0; decide +kernel
      have hl : raw20299step1Labels = raw20299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20299step0 raw20299step0Labels permutation39 permutation2
    mixedMoment B raw20299step1 raw20299step1Labels = mixedMoment B raw20299step2 raw20299step2Labels := by
      have ha : raw20299step2 = -raw20299step1 := by apply Matrix.ext; change ∀ i j, raw20299step2 i j = -(raw20299step1 i j); unfold raw20299step2 raw20299step1; decide +kernel
      have hl : raw20299step2Labels = raw20299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

theorem canonical20300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20300 raw20300Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20300 raw20300Labels = mixedMoment B raw20300step0 raw20300step0Labels := by
      have hz : ∀ j, raw20300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20300step0 = (fun i j => raw20300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20300step0 raw20300; decide +kernel
      have hl : raw20300step0Labels = raw20300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20300 raw20300Labels permutation346 hz
    mixedMoment B raw20300step0 raw20300step0Labels = mixedMoment B raw20300step1 raw20300step1Labels := by
      have ha : raw20300step1 = (fun i j => raw20300step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20300step1 raw20300step0; decide +kernel
      have hl : raw20300step1Labels = raw20300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20300step0 raw20300step0Labels permutation38 permutation2
    mixedMoment B raw20300step1 raw20300step1Labels = mixedMoment B raw20300step2 raw20300step2Labels := by
      have ha : raw20300step2 = -raw20300step1 := by apply Matrix.ext; change ∀ i j, raw20300step2 i j = -(raw20300step1 i j); unfold raw20300step2 raw20300step1; decide +kernel
      have hl : raw20300step2Labels = raw20300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

theorem canonical20301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20301 raw20301Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20301 raw20301Labels = mixedMoment B raw20301step0 raw20301step0Labels := by
      have hz : ∀ j, raw20301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20301step0 = (fun i j => raw20301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20301step0 raw20301; decide +kernel
      have hl : raw20301step0Labels = raw20301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20301 raw20301Labels permutation346 hz
    mixedMoment B raw20301step0 raw20301step0Labels = mixedMoment B raw20301step1 raw20301step1Labels := by
      have ha : raw20301step1 = (fun i j => raw20301step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20301step1 raw20301step0; decide +kernel
      have hl : raw20301step1Labels = raw20301step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20301step0 raw20301step0Labels permutation32 permutation4
    mixedMoment B raw20301step1 raw20301step1Labels = mixedMoment B raw20301step2 raw20301step2Labels := by
      have ha : raw20301step2 = -raw20301step1 := by apply Matrix.ext; change ∀ i j, raw20301step2 i j = -(raw20301step1 i j); unfold raw20301step2 raw20301step1; decide +kernel
      have hl : raw20301step2Labels = raw20301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

theorem canonical20302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20302 raw20302Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20302 raw20302Labels = mixedMoment B raw20302step0 raw20302step0Labels := by
      have hz : ∀ j, raw20302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20302step0 = (fun i j => raw20302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20302step0 raw20302; decide +kernel
      have hl : raw20302step0Labels = raw20302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20302 raw20302Labels permutation346 hz
    mixedMoment B raw20302step0 raw20302step0Labels = mixedMoment B raw20302step1 raw20302step1Labels := by
      have ha : raw20302step1 = (fun i j => raw20302step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20302step1 raw20302step0; decide +kernel
      have hl : raw20302step1Labels = raw20302step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20302step0 raw20302step0Labels permutation34 permutation4
    mixedMoment B raw20302step1 raw20302step1Labels = mixedMoment B raw20302step2 raw20302step2Labels := by
      have ha : raw20302step2 = -raw20302step1 := by apply Matrix.ext; change ∀ i j, raw20302step2 i j = -(raw20302step1 i j); unfold raw20302step2 raw20302step1; decide +kernel
      have hl : raw20302step2Labels = raw20302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical20303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20303 raw20303Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20303 raw20303Labels = mixedMoment B raw20303step0 raw20303step0Labels := by
      have hz : ∀ j, raw20303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20303step0 = (fun i j => raw20303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20303step0 raw20303; decide +kernel
      have hl : raw20303step0Labels = raw20303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303 raw20303Labels permutation434 hz
    mixedMoment B raw20303step0 raw20303step0Labels = mixedMoment B raw20303step1 raw20303step1Labels := by
      have hz : ∀ j, raw20303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20303step1 = (fun i j => raw20303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20303step1 raw20303step0; decide +kernel
      have hl : raw20303step1Labels = raw20303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step0 raw20303step0Labels permutation80 hz
    mixedMoment B raw20303step1 raw20303step1Labels = mixedMoment B raw20303step2 raw20303step2Labels := by
      have hz : ∀ j, raw20303step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20303step2 = (fun i j => raw20303step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20303step2 raw20303step1; decide +kernel
      have hl : raw20303step2Labels = raw20303step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step1 raw20303step1Labels permutation14 hz
    mixedMoment B raw20303step2 raw20303step2Labels = mixedMoment B raw20303step3 raw20303step3Labels := by
      have ha : raw20303step3 = (fun i j => raw20303step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20303step3 raw20303step2; decide +kernel
      have hl : raw20303step3Labels = raw20303step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20303step2 raw20303step2Labels permutation2 permutation4
    mixedMoment B raw20303step3 raw20303step3Labels = mixedMoment B raw20303step4 raw20303step4Labels := by
      have ha : raw20303step4 = -raw20303step3 := by apply Matrix.ext; change ∀ i j, raw20303step4 i j = -(raw20303step3 i j); unfold raw20303step4 raw20303step3; decide +kernel
      have hl : raw20303step4Labels = raw20303step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

theorem canonical20304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20304 raw20304Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20304 raw20304Labels = mixedMoment B raw20304step0 raw20304step0Labels := by
      have hz : ∀ j, raw20304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20304step0 = (fun i j => raw20304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20304step0 raw20304; decide +kernel
      have hl : raw20304step0Labels = raw20304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20304 raw20304Labels permutation434 hz
    mixedMoment B raw20304step0 raw20304step0Labels = mixedMoment B raw20304step1 raw20304step1Labels := by
      have ha : raw20304step1 = (fun i j => raw20304step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20304step1 raw20304step0; decide +kernel
      have hl : raw20304step1Labels = raw20304step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20304step0 raw20304step0Labels permutation34 permutation4
    mixedMoment B raw20304step1 raw20304step1Labels = mixedMoment B raw20304step2 raw20304step2Labels := by
      have ha : raw20304step2 = -raw20304step1 := by apply Matrix.ext; change ∀ i j, raw20304step2 i j = -(raw20304step1 i j); unfold raw20304step2 raw20304step1; decide +kernel
      have hl : raw20304step2Labels = raw20304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical20305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20305 raw20305Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20305 raw20305Labels = mixedMoment B raw20305step0 raw20305step0Labels := by
      have hz : ∀ j, raw20305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20305step0 = (fun i j => raw20305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20305step0 raw20305; decide +kernel
      have hl : raw20305step0Labels = raw20305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20305 raw20305Labels permutation434 hz
    mixedMoment B raw20305step0 raw20305step0Labels = mixedMoment B raw20305step1 raw20305step1Labels := by
      have hz : ∀ j, raw20305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20305step1 = (fun i j => raw20305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20305step1 raw20305step0; decide +kernel
      have hl : raw20305step1Labels = raw20305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20305step0 raw20305step0Labels permutation80 hz
    mixedMoment B raw20305step1 raw20305step1Labels = mixedMoment B raw20305step2 raw20305step2Labels := by
      have ha : raw20305step2 = (fun i j => raw20305step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20305step2 raw20305step1; decide +kernel
      have hl : raw20305step2Labels = raw20305step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20305step1 raw20305step1Labels permutation31 permutation4
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20306 raw20306Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20306 raw20306Labels = mixedMoment B raw20306step0 raw20306step0Labels := by
      have hz : ∀ j, raw20306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20306step0 = (fun i j => raw20306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20306step0 raw20306; decide +kernel
      have hl : raw20306step0Labels = raw20306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20306 raw20306Labels permutation346 hz
    mixedMoment B raw20306step0 raw20306step0Labels = mixedMoment B raw20306step1 raw20306step1Labels := by
      have ha : raw20306step1 = (fun i j => raw20306step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20306step1 raw20306step0; decide +kernel
      have hl : raw20306step1Labels = raw20306step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20306step0 raw20306step0Labels permutation32 permutation4
    mixedMoment B raw20306step1 raw20306step1Labels = mixedMoment B raw20306step2 raw20306step2Labels := by
      have ha : raw20306step2 = -raw20306step1 := by apply Matrix.ext; change ∀ i j, raw20306step2 i j = -(raw20306step1 i j); unfold raw20306step2 raw20306step1; decide +kernel
      have hl : raw20306step2Labels = raw20306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

theorem canonical20307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20307 raw20307Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw20307 raw20307Labels = mixedMoment B raw20307step0 raw20307step0Labels := by
      have ha : raw20307step0 = (fun i j => raw20307 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20307step0 raw20307; decide +kernel
      have hl : raw20307step0Labels = raw20307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20307 raw20307Labels permutation152 permutation4
    mixedMoment B raw20307step0 raw20307step0Labels = mixedMoment B raw20307step1 raw20307step1Labels := by
      have ha : raw20307step1 = -raw20307step0 := by apply Matrix.ext; change ∀ i j, raw20307step1 i j = -(raw20307step0 i j); unfold raw20307step1 raw20307step0; decide +kernel
      have hl : raw20307step1Labels = raw20307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3279 node3279Labels := by rfl

theorem canonical20308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20308 raw20308Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20308 raw20308Labels = mixedMoment B raw20308step0 raw20308step0Labels := by
      have hz : ∀ j, raw20308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20308step0 = (fun i j => raw20308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20308step0 raw20308; decide +kernel
      have hl : raw20308step0Labels = raw20308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20308 raw20308Labels permutation346 hz
    mixedMoment B raw20308step0 raw20308step0Labels = mixedMoment B raw20308step1 raw20308step1Labels := by
      have ha : raw20308step1 = (fun i j => raw20308step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20308step1 raw20308step0; decide +kernel
      have hl : raw20308step1Labels = raw20308step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20308step0 raw20308step0Labels permutation145 permutation4
    _ = mixedMoment B node2005 node2005Labels := by rfl

theorem canonical20309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20309 raw20309Labels = mixedMoment B node1995 node1995Labels := by
  calc
    mixedMoment B raw20309 raw20309Labels = mixedMoment B raw20309step0 raw20309step0Labels := by
      have ha : raw20309step0 = (fun i j => raw20309 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20309step0 raw20309; decide +kernel
      have hl : raw20309step0Labels = raw20309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20309 raw20309Labels permutation662 permutation4
    _ = mixedMoment B node1995 node1995Labels := by rfl

theorem canonical20310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20310 raw20310Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20310 raw20310Labels = mixedMoment B raw20310step0 raw20310step0Labels := by
      have hz : ∀ j, raw20310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20310step0 = (fun i j => raw20310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20310step0 raw20310; decide +kernel
      have hl : raw20310step0Labels = raw20310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20310 raw20310Labels permutation346 hz
    mixedMoment B raw20310step0 raw20310step0Labels = mixedMoment B raw20310step1 raw20310step1Labels := by
      have ha : raw20310step1 = (fun i j => raw20310step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20310step1 raw20310step0; decide +kernel
      have hl : raw20310step1Labels = raw20310step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20310step0 raw20310step0Labels permutation145 permutation4
    _ = mixedMoment B node2045 node2045Labels := by rfl

theorem canonical20311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20311 raw20311Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw20311 raw20311Labels = mixedMoment B raw20311step0 raw20311step0Labels := by
      have hz : ∀ j, raw20311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20311step0 = (fun i j => raw20311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20311step0 raw20311; decide +kernel
      have hl : raw20311step0Labels = raw20311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20311 raw20311Labels permutation346 hz
    mixedMoment B raw20311step0 raw20311step0Labels = mixedMoment B raw20311step1 raw20311step1Labels := by
      have ha : raw20311step1 = (fun i j => raw20311step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20311step1 raw20311step0; decide +kernel
      have hl : raw20311step1Labels = raw20311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20311step0 raw20311step0Labels permutation151 permutation2
    mixedMoment B raw20311step1 raw20311step1Labels = mixedMoment B raw20311step2 raw20311step2Labels := by
      have ha : raw20311step2 = -raw20311step1 := by apply Matrix.ext; change ∀ i j, raw20311step2 i j = -(raw20311step1 i j); unfold raw20311step2 raw20311step1; decide +kernel
      have hl : raw20311step2Labels = raw20311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2087 node2087Labels := by rfl

theorem canonical20312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20312 raw20312Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw20312 raw20312Labels = mixedMoment B raw20312step0 raw20312step0Labels := by
      have ha : raw20312step0 = (fun i j => raw20312 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20312step0 raw20312; decide +kernel
      have hl : raw20312step0Labels = raw20312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20312 raw20312Labels permutation676 permutation2
    mixedMoment B raw20312step0 raw20312step0Labels = mixedMoment B raw20312step1 raw20312step1Labels := by
      have ha : raw20312step1 = -raw20312step0 := by apply Matrix.ext; change ∀ i j, raw20312step1 i j = -(raw20312step0 i j); unfold raw20312step1 raw20312step0; decide +kernel
      have hl : raw20312step1Labels = raw20312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2070 node2070Labels := by rfl

theorem canonical20313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20313 raw20313Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw20313 raw20313Labels = mixedMoment B raw20313step0 raw20313step0Labels := by
      have hz : ∀ j, raw20313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20313step0 = (fun i j => raw20313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20313step0 raw20313; decide +kernel
      have hl : raw20313step0Labels = raw20313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20313 raw20313Labels permutation346 hz
    mixedMoment B raw20313step0 raw20313step0Labels = mixedMoment B raw20313step1 raw20313step1Labels := by
      have ha : raw20313step1 = (fun i j => raw20313step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20313step1 raw20313step0; decide +kernel
      have hl : raw20313step1Labels = raw20313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20313step0 raw20313step0Labels permutation149 permutation2
    mixedMoment B raw20313step1 raw20313step1Labels = mixedMoment B raw20313step2 raw20313step2Labels := by
      have ha : raw20313step2 = -raw20313step1 := by apply Matrix.ext; change ∀ i j, raw20313step2 i j = -(raw20313step1 i j); unfold raw20313step2 raw20313step1; decide +kernel
      have hl : raw20313step2Labels = raw20313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical20314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20314 raw20314Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw20314 raw20314Labels = mixedMoment B raw20314step0 raw20314step0Labels := by
      have hz : ∀ j, raw20314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20314step0 = (fun i j => raw20314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20314step0 raw20314; decide +kernel
      have hl : raw20314step0Labels = raw20314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20314 raw20314Labels permutation346 hz
    mixedMoment B raw20314step0 raw20314step0Labels = mixedMoment B raw20314step1 raw20314step1Labels := by
      have ha : raw20314step1 = (fun i j => raw20314step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20314step1 raw20314step0; decide +kernel
      have hl : raw20314step1Labels = raw20314step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20314step0 raw20314step0Labels permutation38 permutation2
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical20315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20315 raw20315Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw20315 raw20315Labels = mixedMoment B raw20315step0 raw20315step0Labels := by
      have hz : ∀ j, raw20315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20315step0 = (fun i j => raw20315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20315step0 raw20315; decide +kernel
      have hl : raw20315step0Labels = raw20315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20315 raw20315Labels permutation346 hz
    mixedMoment B raw20315step0 raw20315step0Labels = mixedMoment B raw20315step1 raw20315step1Labels := by
      have ha : raw20315step1 = (fun i j => raw20315step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20315step1 raw20315step0; decide +kernel
      have hl : raw20315step1Labels = raw20315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20315step0 raw20315step0Labels permutation38 permutation2
    _ = mixedMoment B node1181 node1181Labels := by rfl

theorem canonical20316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20316 raw20316Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw20316 raw20316Labels = mixedMoment B raw20316step0 raw20316step0Labels := by
      have hz : ∀ j, raw20316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20316step0 = (fun i j => raw20316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20316step0 raw20316; decide +kernel
      have hl : raw20316step0Labels = raw20316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20316 raw20316Labels permutation346 hz
    mixedMoment B raw20316step0 raw20316step0Labels = mixedMoment B raw20316step1 raw20316step1Labels := by
      have ha : raw20316step1 = (fun i j => raw20316step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20316step1 raw20316step0; decide +kernel
      have hl : raw20316step1Labels = raw20316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20316step0 raw20316step0Labels permutation151 permutation2
    mixedMoment B raw20316step1 raw20316step1Labels = mixedMoment B raw20316step2 raw20316step2Labels := by
      have ha : raw20316step2 = -raw20316step1 := by apply Matrix.ext; change ∀ i j, raw20316step2 i j = -(raw20316step1 i j); unfold raw20316step2 raw20316step1; decide +kernel
      have hl : raw20316step2Labels = raw20316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2492 node2492Labels := by rfl

theorem canonical20317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20317 raw20317Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw20317 raw20317Labels = mixedMoment B raw20317step0 raw20317step0Labels := by
      have ha : raw20317step0 = (fun i j => raw20317 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20317step0 raw20317; decide +kernel
      have hl : raw20317step0Labels = raw20317Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20317 raw20317Labels permutation676 permutation2
    mixedMoment B raw20317step0 raw20317step0Labels = mixedMoment B raw20317step1 raw20317step1Labels := by
      have ha : raw20317step1 = -raw20317step0 := by apply Matrix.ext; change ∀ i j, raw20317step1 i j = -(raw20317step0 i j); unfold raw20317step1 raw20317step0; decide +kernel
      have hl : raw20317step1Labels = raw20317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2453 node2453Labels := by rfl

theorem canonical20318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20318 raw20318Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw20318 raw20318Labels = mixedMoment B raw20318step0 raw20318step0Labels := by
      have hz : ∀ j, raw20318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20318step0 = (fun i j => raw20318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20318step0 raw20318; decide +kernel
      have hl : raw20318step0Labels = raw20318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20318 raw20318Labels permutation346 hz
    mixedMoment B raw20318step0 raw20318step0Labels = mixedMoment B raw20318step1 raw20318step1Labels := by
      have ha : raw20318step1 = (fun i j => raw20318step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20318step1 raw20318step0; decide +kernel
      have hl : raw20318step1Labels = raw20318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20318step0 raw20318step0Labels permutation38 permutation2
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical20319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20319 raw20319Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw20319 raw20319Labels = mixedMoment B raw20319step0 raw20319step0Labels := by
      have hz : ∀ j, raw20319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20319step0 = (fun i j => raw20319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20319step0 raw20319; decide +kernel
      have hl : raw20319step0Labels = raw20319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20319 raw20319Labels permutation346 hz
    mixedMoment B raw20319step0 raw20319step0Labels = mixedMoment B raw20319step1 raw20319step1Labels := by
      have ha : raw20319step1 = (fun i j => raw20319step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20319step1 raw20319step0; decide +kernel
      have hl : raw20319step1Labels = raw20319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20319step0 raw20319step0Labels permutation38 permutation2
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical20320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20320 raw20320Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw20320 raw20320Labels = mixedMoment B raw20320step0 raw20320step0Labels := by
      have hz : ∀ j, raw20320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20320step0 = (fun i j => raw20320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20320step0 raw20320; decide +kernel
      have hl : raw20320step0Labels = raw20320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20320 raw20320Labels permutation346 hz
    mixedMoment B raw20320step0 raw20320step0Labels = mixedMoment B raw20320step1 raw20320step1Labels := by
      have ha : raw20320step1 = (fun i j => raw20320step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20320step1 raw20320step0; decide +kernel
      have hl : raw20320step1Labels = raw20320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20320step0 raw20320step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical20321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20321 raw20321Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw20321 raw20321Labels = mixedMoment B raw20321step0 raw20321step0Labels := by
      have hz : ∀ j, raw20321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20321step0 = (fun i j => raw20321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20321step0 raw20321; decide +kernel
      have hl : raw20321step0Labels = raw20321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20321 raw20321Labels permutation346 hz
    mixedMoment B raw20321step0 raw20321step0Labels = mixedMoment B raw20321step1 raw20321step1Labels := by
      have ha : raw20321step1 = (fun i j => raw20321step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20321step1 raw20321step0; decide +kernel
      have hl : raw20321step1Labels = raw20321step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20321step0 raw20321step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9826 raw9826Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9826 raw9826Labels = mixedMoment B raw9826step0 raw9826step0Labels := by
      have hz : ∀ j, raw9826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9826step0 = (fun i j => raw9826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9826step0 raw9826; decide +kernel
      have hl : raw9826step0Labels = raw9826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9826 raw9826Labels permutation346 hz
    mixedMoment B raw9826step0 raw9826step0Labels = mixedMoment B raw9826step1 raw9826step1Labels := by
      have ha : raw9826step1 = (fun i j => raw9826step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9826step1 raw9826step0; decide +kernel
      have hl : raw9826step1Labels = raw9826step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9826step0 raw9826step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9827 raw9827Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw9827 raw9827Labels = mixedMoment B raw9827step0 raw9827step0Labels := by
      have hz : ∀ j, raw9827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9827step0 = (fun i j => raw9827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9827step0 raw9827; decide +kernel
      have hl : raw9827step0Labels = raw9827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9827 raw9827Labels permutation346 hz
    mixedMoment B raw9827step0 raw9827step0Labels = mixedMoment B raw9827step1 raw9827step1Labels := by
      have ha : raw9827step1 = (fun i j => raw9827step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9827step1 raw9827step0; decide +kernel
      have hl : raw9827step1Labels = raw9827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9827step0 raw9827step0Labels permutation38 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical9831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9831 raw9831Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw9831 raw9831Labels = mixedMoment B raw9831step0 raw9831step0Labels := by
      have hz : ∀ j, raw9831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9831step0 = (fun i j => raw9831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9831step0 raw9831; decide +kernel
      have hl : raw9831step0Labels = raw9831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9831 raw9831Labels permutation346 hz
    mixedMoment B raw9831step0 raw9831step0Labels = mixedMoment B raw9831step1 raw9831step1Labels := by
      have ha : raw9831step1 = (fun i j => raw9831step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9831step1 raw9831step0; decide +kernel
      have hl : raw9831step1Labels = raw9831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9831step0 raw9831step0Labels permutation38 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical9845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9845 raw9845Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw9845 raw9845Labels = mixedMoment B raw9845step0 raw9845step0Labels := by
      have hz : ∀ j, raw9845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9845step0 = (fun i j => raw9845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9845step0 raw9845; decide +kernel
      have hl : raw9845step0Labels = raw9845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9845 raw9845Labels permutation346 hz
    mixedMoment B raw9845step0 raw9845step0Labels = mixedMoment B raw9845step1 raw9845step1Labels := by
      have ha : raw9845step1 = (fun i j => raw9845step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9845step1 raw9845step0; decide +kernel
      have hl : raw9845step1Labels = raw9845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9845step0 raw9845step0Labels permutation38 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1111 node1111Labels = Sparse.eval nodeValue1111 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1111) = mixedMoment B node1111 node1111Labels := rfl
  simpa [nodeValue1111, Sparse.eval] using hc.symm

theorem sound1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1112 node1112Labels = Sparse.eval nodeValue1112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1112) = mixedMoment B node1112 node1112Labels := rfl
  simpa [nodeValue1112, Sparse.eval] using hc.symm

theorem sound1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1115 node1115Labels = Sparse.eval nodeValue1115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1115) = mixedMoment B node1115 node1115Labels := rfl
  simpa [nodeValue1115, Sparse.eval] using hc.symm

theorem sound1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1118 node1118Labels = Sparse.eval nodeValue1118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1118) = mixedMoment B node1118 node1118Labels := rfl
  simpa [nodeValue1118, Sparse.eval] using hc.symm

theorem sound1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1119 node1119Labels = Sparse.eval nodeValue1119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1119) = mixedMoment B node1119 node1119Labels := rfl
  simpa [nodeValue1119, Sparse.eval] using hc.symm

theorem sound1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1120 node1120Labels = Sparse.eval nodeValue1120 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1120) = mixedMoment B node1120 node1120Labels := rfl
  simpa [nodeValue1120, Sparse.eval] using hc.symm

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1136 node1136Labels = Sparse.eval nodeValue1136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1136) = mixedMoment B node1136 node1136Labels := rfl
  simpa [nodeValue1136, Sparse.eval] using hc.symm

theorem sound1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1148 node1148Labels = Sparse.eval nodeValue1148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1148) = mixedMoment B node1148 node1148Labels := rfl
  simpa [nodeValue1148, Sparse.eval] using hc.symm

theorem sound1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1150 node1150Labels = Sparse.eval nodeValue1150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1150) = mixedMoment B node1150 node1150Labels := rfl
  simpa [nodeValue1150, Sparse.eval] using hc.symm

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

theorem sound1181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1181 node1181Labels = Sparse.eval nodeValue1181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1181) = mixedMoment B node1181 node1181Labels := rfl
  simpa [nodeValue1181, Sparse.eval] using hc.symm

theorem sound1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1211 node1211Labels = Sparse.eval nodeValue1211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1211) = mixedMoment B node1211 node1211Labels := rfl
  simpa [nodeValue1211, Sparse.eval] using hc.symm

theorem sound1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1215 node1215Labels = Sparse.eval nodeValue1215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1215) = mixedMoment B node1215 node1215Labels := rfl
  simpa [nodeValue1215, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1217 node1217Labels = Sparse.eval nodeValue1217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1217) = mixedMoment B node1217 node1217Labels := rfl
  simpa [nodeValue1217, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1258 node1258Labels = Sparse.eval nodeValue1258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1258) = mixedMoment B node1258 node1258Labels := rfl
  simpa [nodeValue1258, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1596 node1596Labels = 0 := by
  exact mixedMoment_alpha B hF node1596 node1596Labels 1 permutation437
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1596 node1596Labels = Sparse.eval nodeValue1596 (mixedVector B) := by
  simpa only [nodeValue1596, Sparse.eval_nil] using zero1596 B _hB _hF

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1604 node1604Labels = Sparse.eval nodeValue1604 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1604) = mixedMoment B node1604 node1604Labels := rfl
  simpa [nodeValue1604, Sparse.eval] using hc.symm

theorem sound1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1613 node1613Labels = Sparse.eval nodeValue1613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1613) = mixedMoment B node1613 node1613Labels := rfl
  simpa [nodeValue1613, Sparse.eval] using hc.symm

theorem sound1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1617 node1617Labels = Sparse.eval nodeValue1617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1617) = mixedMoment B node1617 node1617Labels := rfl
  simpa [nodeValue1617, Sparse.eval] using hc.symm

theorem sound1619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1619 node1619Labels = Sparse.eval nodeValue1619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1619) = mixedMoment B node1619 node1619Labels := rfl
  simpa [nodeValue1619, Sparse.eval] using hc.symm

theorem sound1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1624 node1624Labels = Sparse.eval nodeValue1624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1624) = mixedMoment B node1624 node1624Labels := rfl
  simpa [nodeValue1624, Sparse.eval] using hc.symm

theorem sound1628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1628 node1628Labels = Sparse.eval nodeValue1628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1628) = mixedMoment B node1628 node1628Labels := rfl
  simpa [nodeValue1628, Sparse.eval] using hc.symm

theorem sound1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1630 node1630Labels = Sparse.eval nodeValue1630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1630) = mixedMoment B node1630 node1630Labels := rfl
  simpa [nodeValue1630, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1995 node1995Labels = Sparse.eval nodeValue1995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1995) = mixedMoment B node1995 node1995Labels := rfl
  simpa [nodeValue1995, Sparse.eval] using hc.symm

theorem sound2005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2005 node2005Labels = Sparse.eval nodeValue2005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2005) = mixedMoment B node2005 node2005Labels := rfl
  simpa [nodeValue2005, Sparse.eval] using hc.symm

theorem sound2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2045 node2045Labels = Sparse.eval nodeValue2045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2045) = mixedMoment B node2045 node2045Labels := rfl
  simpa [nodeValue2045, Sparse.eval] using hc.symm

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

theorem sound2070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2070 node2070Labels = Sparse.eval nodeValue2070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2070) = mixedMoment B node2070 node2070Labels := rfl
  simpa [nodeValue2070, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

theorem sound2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2087 node2087Labels = Sparse.eval nodeValue2087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2087) = mixedMoment B node2087 node2087Labels := rfl
  simpa [nodeValue2087, Sparse.eval] using hc.symm

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

theorem sound2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2119 node2119Labels = Sparse.eval nodeValue2119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2119) = mixedMoment B node2119 node2119Labels := rfl
  simpa [nodeValue2119, Sparse.eval] using hc.symm

theorem sound2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2130 node2130Labels = Sparse.eval nodeValue2130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2130) = mixedMoment B node2130 node2130Labels := rfl
  simpa [nodeValue2130, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

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

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

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

theorem sound2453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2453 node2453Labels = Sparse.eval nodeValue2453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2453) = mixedMoment B node2453 node2453Labels := rfl
  simpa [nodeValue2453, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2492 node2492Labels = Sparse.eval nodeValue2492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2492) = mixedMoment B node2492 node2492Labels := rfl
  simpa [nodeValue2492, Sparse.eval] using hc.symm

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

theorem sound2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2664 node2664Labels = Sparse.eval nodeValue2664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2664) = mixedMoment B node2664 node2664Labels := rfl
  simpa [nodeValue2664, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2761 node2761Labels = Sparse.eval nodeValue2761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2761) = mixedMoment B node2761 node2761Labels := rfl
  simpa [nodeValue2761, Sparse.eval] using hc.symm

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

theorem sound3242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3242 node3242Labels = Sparse.eval nodeValue3242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3242) = mixedMoment B node3242 node3242Labels := rfl
  simpa [nodeValue3242, Sparse.eval] using hc.symm

theorem sound3247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3247 node3247Labels = Sparse.eval nodeValue3247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3247) = mixedMoment B node3247 node3247Labels := rfl
  simpa [nodeValue3247, Sparse.eval] using hc.symm

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

theorem sound3279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3279 node3279Labels = Sparse.eval nodeValue3279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3279) = mixedMoment B node3279 node3279Labels := rfl
  simpa [nodeValue3279, Sparse.eval] using hc.symm

theorem sound3283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3283 node3283Labels = Sparse.eval nodeValue3283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3283) = mixedMoment B node3283 node3283Labels := rfl
  simpa [nodeValue3283, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

theorem sound3310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3310 node3310Labels = Sparse.eval nodeValue3310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3310) = mixedMoment B node3310 node3310Labels := rfl
  simpa [nodeValue3310, Sparse.eval] using hc.symm

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node626 node626Labels = Sparse.eval nodeValue626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 626) = mixedMoment B node626 node626Labels := rfl
  simpa [nodeValue626, Sparse.eval] using hc.symm

theorem sound630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node630 node630Labels = Sparse.eval nodeValue630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 630) = mixedMoment B node630 node630Labels := rfl
  simpa [nodeValue630, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources38
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1241 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1241 + difference 0 0) (sourceB1241 + difference 0 0) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1241 + difference 0 0) (sourceB1241 + difference 0 0) sourceC1241) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1241 + difference 1 0) (sourceB1241 + difference 0 1) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1241 + difference 1 0) (sourceB1241 + difference 0 1) sourceC1241) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1241 + difference 2 0) (sourceB1241 + difference 0 2) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1241 + difference 2 0) (sourceB1241 + difference 0 2) sourceC1241) = raw20261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20261; decide +kernel
    rw [ha]
    exact (canonical20261 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1241 + difference 3 0) (sourceB1241 + difference 0 3) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1241 + difference 3 0) (sourceB1241 + difference 0 3) sourceC1241) = raw20134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20134; decide +kernel
    rw [ha]
    exact (canonical20134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1241 + difference 4 0) (sourceB1241 + difference 0 4) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1241 + difference 4 0) (sourceB1241 + difference 0 4) sourceC1241) = raw20105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20105; decide +kernel
    rw [ha]
    exact (canonical20105 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1241 + difference 5 0) (sourceB1241 + difference 0 5) sourceC1241) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1241 + difference 5 0) (sourceB1241 + difference 0 5) sourceC1241) = raw20262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1241 sourceB1241 sourceC1241 difference raw20262; decide +kernel
    rw [ha]
    exact (canonical20262 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1241 + sourceB1241) sourceC1241) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1241 + sourceB1241) sourceC1241) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1241 sourceB1241 sourceC1241 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1241 sourceB1241 sourceC1241
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1241, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1242 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 0) (sourceB1242 + difference 0 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 0) (sourceB1242 + difference 0 1) sourceC1242) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 1) (sourceB1242 + difference 1 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 1) (sourceB1242 + difference 1 1) sourceC1242) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 2) (sourceB1242 + difference 2 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 2) (sourceB1242 + difference 2 1) sourceC1242) = raw20263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20263; decide +kernel
    rw [ha]
    exact (canonical20263 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 3) (sourceB1242 + difference 3 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 3) (sourceB1242 + difference 3 1) sourceC1242) = raw20264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20264; decide +kernel
    rw [ha]
    exact (canonical20264 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 4) (sourceB1242 + difference 4 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 4) (sourceB1242 + difference 4 1) sourceC1242) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1242 + difference 1 5) (sourceB1242 + difference 5 1) sourceC1242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1242 + difference 1 5) (sourceB1242 + difference 5 1) sourceC1242) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1242 sourceB1242 sourceC1242 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1242 + sourceB1242) sourceC1242) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1242 + sourceB1242) sourceC1242) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1242 sourceB1242 sourceC1242 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1242 sourceB1242 sourceC1242
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1242, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1243 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1243 + difference 0 4) (sourceB1243 + difference 4 0) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1243 + difference 0 4) (sourceB1243 + difference 4 0) sourceC1243) = raw20259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20259; decide +kernel
    rw [ha]
    exact (canonical20259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1243 + difference 1 4) (sourceB1243 + difference 4 1) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1243 + difference 1 4) (sourceB1243 + difference 4 1) sourceC1243) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1243 + difference 2 4) (sourceB1243 + difference 4 2) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1243 + difference 2 4) (sourceB1243 + difference 4 2) sourceC1243) = raw20266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20266; decide +kernel
    rw [ha]
    exact (canonical20266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1243 + difference 3 4) (sourceB1243 + difference 4 3) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1243 + difference 3 4) (sourceB1243 + difference 4 3) sourceC1243) = raw20267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20267; decide +kernel
    rw [ha]
    exact (canonical20267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1243 + difference 4 4) (sourceB1243 + difference 4 4) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1243 + difference 4 4) (sourceB1243 + difference 4 4) sourceC1243) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1243 + difference 5 4) (sourceB1243 + difference 4 5) sourceC1243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1243 + difference 5 4) (sourceB1243 + difference 4 5) sourceC1243) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1243 sourceB1243 sourceC1243 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1243 + sourceB1243) sourceC1243) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1243 + sourceB1243) sourceC1243) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1243 sourceB1243 sourceC1243 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1243 sourceB1243 sourceC1243
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1243, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1244 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 0) (sourceB1244 + difference 0 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 0) (sourceB1244 + difference 0 5) sourceC1244) = raw20262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20262; decide +kernel
    rw [ha]
    exact (canonical20262 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 1) (sourceB1244 + difference 1 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 1) (sourceB1244 + difference 1 5) sourceC1244) = raw20269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20269; decide +kernel
    rw [ha]
    exact (canonical20269 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 2) (sourceB1244 + difference 2 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 2) (sourceB1244 + difference 2 5) sourceC1244) = raw20270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20270; decide +kernel
    rw [ha]
    exact (canonical20270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 3) (sourceB1244 + difference 3 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 3) (sourceB1244 + difference 3 5) sourceC1244) = raw20271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20271; decide +kernel
    rw [ha]
    exact (canonical20271 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 4) (sourceB1244 + difference 4 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 4) (sourceB1244 + difference 4 5) sourceC1244) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1244 + difference 5 5) (sourceB1244 + difference 5 5) sourceC1244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1244 + difference 5 5) (sourceB1244 + difference 5 5) sourceC1244) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1244 sourceB1244 sourceC1244 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1244 + sourceB1244) sourceC1244) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1244 + sourceB1244) sourceC1244) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1244 sourceB1244 sourceC1244 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1244 sourceB1244 sourceC1244
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1244, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1246 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 0) (sourceB1246 + difference 0 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 0) (sourceB1246 + difference 0 0) sourceC1246) = raw19492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw19492; decide +kernel
    rw [ha]
    exact (canonical19492 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 1) (sourceB1246 + difference 1 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 1) (sourceB1246 + difference 1 0) sourceC1246) = raw20273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20273; decide +kernel
    rw [ha]
    exact (canonical20273 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 2) (sourceB1246 + difference 2 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 2) (sourceB1246 + difference 2 0) sourceC1246) = raw20274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20274; decide +kernel
    rw [ha]
    exact (canonical20274 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 3) (sourceB1246 + difference 3 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 3) (sourceB1246 + difference 3 0) sourceC1246) = raw20275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20275; decide +kernel
    rw [ha]
    exact (canonical20275 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 4) (sourceB1246 + difference 4 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 4) (sourceB1246 + difference 4 0) sourceC1246) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1246 + difference 0 5) (sourceB1246 + difference 5 0) sourceC1246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1246 + difference 0 5) (sourceB1246 + difference 5 0) sourceC1246) = raw20276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1246 sourceB1246 sourceC1246 difference raw20276; decide +kernel
    rw [ha]
    exact (canonical20276 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1246 + sourceB1246) sourceC1246) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1246 + sourceB1246) sourceC1246) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1246 sourceB1246 sourceC1246 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1246 sourceB1246 sourceC1246
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1246, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1247 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1247 + difference 0 1) (sourceB1247 + difference 1 0) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1247 + difference 0 1) (sourceB1247 + difference 1 0) sourceC1247) = raw20277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20277; decide +kernel
    rw [ha]
    exact (canonical20277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1247 + difference 1 1) (sourceB1247 + difference 1 1) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1247 + difference 1 1) (sourceB1247 + difference 1 1) sourceC1247) = raw20278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20278; decide +kernel
    rw [ha]
    exact (canonical20278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1247 + difference 2 1) (sourceB1247 + difference 1 2) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA1247 + difference 2 1) (sourceB1247 + difference 1 2) sourceC1247) = raw20279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20279; decide +kernel
    rw [ha]
    exact (canonical20279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1247 + difference 3 1) (sourceB1247 + difference 1 3) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1247 + difference 3 1) (sourceB1247 + difference 1 3) sourceC1247) = raw20280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20280; decide +kernel
    rw [ha]
    exact (canonical20280 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1247 + difference 4 1) (sourceB1247 + difference 1 4) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1247 + difference 4 1) (sourceB1247 + difference 1 4) sourceC1247) = raw20281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20281; decide +kernel
    rw [ha]
    exact (canonical20281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1247 + difference 5 1) (sourceB1247 + difference 1 5) sourceC1247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1247 + difference 5 1) (sourceB1247 + difference 1 5) sourceC1247) = raw20282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1247 sourceB1247 sourceC1247 difference raw20282; decide +kernel
    rw [ha]
    exact (canonical20282 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1247 + sourceB1247) sourceC1247) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1247 + sourceB1247) sourceC1247) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1247 sourceB1247 sourceC1247 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1247 sourceB1247 sourceC1247
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1247, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1248 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 0) (sourceB1248 + difference 0 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 0) (sourceB1248 + difference 0 3) sourceC1248) = raw20284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20284; decide +kernel
    rw [ha]
    exact (canonical20284 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 1) (sourceB1248 + difference 1 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 1) (sourceB1248 + difference 1 3) sourceC1248) = raw20280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20280; decide +kernel
    rw [ha]
    exact (canonical20280 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 2) (sourceB1248 + difference 2 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 2) (sourceB1248 + difference 2 3) sourceC1248) = raw20285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20285; decide +kernel
    rw [ha]
    exact (canonical20285 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 3) (sourceB1248 + difference 3 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 3) (sourceB1248 + difference 3 3) sourceC1248) = raw20278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20278; decide +kernel
    rw [ha]
    exact (canonical20278 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 4) (sourceB1248 + difference 4 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 4) (sourceB1248 + difference 4 3) sourceC1248) = raw20286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20286; decide +kernel
    rw [ha]
    exact (canonical20286 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 5) (sourceB1248 + difference 5 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 5) (sourceB1248 + difference 5 3) sourceC1248) = raw20287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20287; decide +kernel
    rw [ha]
    exact (canonical20287 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1248 + sourceB1248) sourceC1248) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1248 + sourceB1248) sourceC1248) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1248 sourceB1248 sourceC1248 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1248 sourceB1248 sourceC1248
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1248, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1249 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 0) (sourceB1249 + difference 0 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 0) (sourceB1249 + difference 0 1) sourceC1249) = raw20288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20288; decide +kernel
    rw [ha]
    exact (canonical20288 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 1) (sourceB1249 + difference 1 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 1) (sourceB1249 + difference 1 1) sourceC1249) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 2) (sourceB1249 + difference 2 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 2) (sourceB1249 + difference 2 1) sourceC1249) = raw20289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20289; decide +kernel
    rw [ha]
    exact (canonical20289 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 3) (sourceB1249 + difference 3 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 3) (sourceB1249 + difference 3 1) sourceC1249) = raw20290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20290; decide +kernel
    rw [ha]
    exact (canonical20290 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 4) (sourceB1249 + difference 4 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 4) (sourceB1249 + difference 4 1) sourceC1249) = raw20291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20291; decide +kernel
    rw [ha]
    exact (canonical20291 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 5) (sourceB1249 + difference 5 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 5) (sourceB1249 + difference 5 1) sourceC1249) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1249 + sourceB1249) sourceC1249) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1249 + sourceB1249) sourceC1249) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA1249 sourceB1249 sourceC1249 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1249 sourceB1249 sourceC1249
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1249, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1250 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1250 + difference 0 3) (sourceB1250 + difference 3 0) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1250 + difference 0 3) (sourceB1250 + difference 3 0) sourceC1250) = raw9845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw9845; decide +kernel
    rw [ha]
    exact (canonical9845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1250 + difference 1 3) (sourceB1250 + difference 3 1) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1250 + difference 1 3) (sourceB1250 + difference 3 1) sourceC1250) = raw20290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20290; decide +kernel
    rw [ha]
    exact (canonical20290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1250 + difference 2 3) (sourceB1250 + difference 3 2) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1250 + difference 2 3) (sourceB1250 + difference 3 2) sourceC1250) = raw20292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20292; decide +kernel
    rw [ha]
    exact (canonical20292 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1250 + difference 3 3) (sourceB1250 + difference 3 3) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1250 + difference 3 3) (sourceB1250 + difference 3 3) sourceC1250) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1250 + difference 4 3) (sourceB1250 + difference 3 4) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1250 + difference 4 3) (sourceB1250 + difference 3 4) sourceC1250) = raw20293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20293; decide +kernel
    rw [ha]
    exact (canonical20293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1250 + difference 5 3) (sourceB1250 + difference 3 5) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1250 + difference 5 3) (sourceB1250 + difference 3 5) sourceC1250) = raw20294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20294; decide +kernel
    rw [ha]
    exact (canonical20294 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1250 + sourceB1250) sourceC1250) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1250 + sourceB1250) sourceC1250) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA1250 sourceB1250 sourceC1250 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1250 sourceB1250 sourceC1250
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1250, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 0) (sourceB1251 + difference 0 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 0) (sourceB1251 + difference 0 0) sourceC1251) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 1) (sourceB1251 + difference 1 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 1) (sourceB1251 + difference 1 0) sourceC1251) = raw20296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20296; decide +kernel
    rw [ha]
    exact (canonical20296 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 2) (sourceB1251 + difference 2 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 2) (sourceB1251 + difference 2 0) sourceC1251) = raw20297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20297; decide +kernel
    rw [ha]
    exact (canonical20297 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 3) (sourceB1251 + difference 3 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 3) (sourceB1251 + difference 3 0) sourceC1251) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 4) (sourceB1251 + difference 4 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 4) (sourceB1251 + difference 4 0) sourceC1251) = raw20299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20299; decide +kernel
    rw [ha]
    exact (canonical20299 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 5) (sourceB1251 + difference 5 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 5) (sourceB1251 + difference 5 0) sourceC1251) = raw20300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20300; decide +kernel
    rw [ha]
    exact (canonical20300 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1251 + sourceB1251) sourceC1251) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1251 + sourceB1251) sourceC1251) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1251 sourceB1251 sourceC1251 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1251 sourceB1251 sourceC1251
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1251, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1252 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1252 + difference 0 0) (sourceB1252 + difference 0 0) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1252 + difference 0 0) (sourceB1252 + difference 0 0) sourceC1252) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1252 + difference 1 0) (sourceB1252 + difference 0 1) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1252 + difference 1 0) (sourceB1252 + difference 0 1) sourceC1252) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1252 + difference 2 0) (sourceB1252 + difference 0 2) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1596) := by
    have ha : (tripleCharges (sourceA1252 + difference 2 0) (sourceB1252 + difference 0 2) sourceC1252) = raw20212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20212; decide +kernel
    rw [ha]
    exact (canonical20212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1252 + difference 3 0) (sourceB1252 + difference 0 3) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1252 + difference 3 0) (sourceB1252 + difference 0 3) sourceC1252) = raw20164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20164; decide +kernel
    rw [ha]
    exact (canonical20164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1252 + difference 4 0) (sourceB1252 + difference 0 4) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1252 + difference 4 0) (sourceB1252 + difference 0 4) sourceC1252) = raw20301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20301; decide +kernel
    rw [ha]
    exact (canonical20301 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1252 + difference 5 0) (sourceB1252 + difference 0 5) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1252 + difference 5 0) (sourceB1252 + difference 0 5) sourceC1252) = raw20302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20302; decide +kernel
    rw [ha]
    exact (canonical20302 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1252 + sourceB1252) sourceC1252) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1252 + sourceB1252) sourceC1252) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1252 sourceB1252 sourceC1252 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1252 sourceB1252 sourceC1252
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1252, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1253 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1253 + difference 0 3) (sourceB1253 + difference 3 0) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1253 + difference 0 3) (sourceB1253 + difference 3 0) sourceC1253) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1253 + difference 1 3) (sourceB1253 + difference 3 1) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1253 + difference 1 3) (sourceB1253 + difference 3 1) sourceC1253) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1253 + difference 2 3) (sourceB1253 + difference 3 2) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1253 + difference 2 3) (sourceB1253 + difference 3 2) sourceC1253) = raw20304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20304; decide +kernel
    rw [ha]
    exact (canonical20304 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1253 + difference 3 3) (sourceB1253 + difference 3 3) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1253 + difference 3 3) (sourceB1253 + difference 3 3) sourceC1253) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1253 + difference 4 3) (sourceB1253 + difference 3 4) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1253 + difference 4 3) (sourceB1253 + difference 3 4) sourceC1253) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1253 + difference 5 3) (sourceB1253 + difference 3 5) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1253 + difference 5 3) (sourceB1253 + difference 3 5) sourceC1253) = raw20305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20305; decide +kernel
    rw [ha]
    exact (canonical20305 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1253 + sourceB1253) sourceC1253) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1253 + sourceB1253) sourceC1253) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1253 sourceB1253 sourceC1253 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1253 sourceB1253 sourceC1253
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1253, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 0) (sourceB1254 + difference 0 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 0) (sourceB1254 + difference 0 4) sourceC1254) = raw20301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20301; decide +kernel
    rw [ha]
    exact (canonical20301 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 1) (sourceB1254 + difference 1 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 1) (sourceB1254 + difference 1 4) sourceC1254) = raw20306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20306; decide +kernel
    rw [ha]
    exact (canonical20306 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 2) (sourceB1254 + difference 2 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 2) (sourceB1254 + difference 2 4) sourceC1254) = raw20307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20307; decide +kernel
    rw [ha]
    exact (canonical20307 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 3) (sourceB1254 + difference 3 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 3) (sourceB1254 + difference 3 4) sourceC1254) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 4) (sourceB1254 + difference 4 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 4) (sourceB1254 + difference 4 4) sourceC1254) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 5) (sourceB1254 + difference 5 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 5) (sourceB1254 + difference 5 4) sourceC1254) = raw20267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20267; decide +kernel
    rw [ha]
    exact (canonical20267 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1254 + sourceB1254) sourceC1254) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1254 + sourceB1254) sourceC1254) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1254 sourceB1254 sourceC1254 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1254 sourceB1254 sourceC1254
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1254, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 0) (sourceB1255 + difference 0 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 0) (sourceB1255 + difference 0 5) sourceC1255) = raw20302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20302; decide +kernel
    rw [ha]
    exact (canonical20302 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 1) (sourceB1255 + difference 1 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 1) (sourceB1255 + difference 1 5) sourceC1255) = raw20308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20308; decide +kernel
    rw [ha]
    exact (canonical20308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 2) (sourceB1255 + difference 2 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1995) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 2) (sourceB1255 + difference 2 5) sourceC1255) = raw20309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20309; decide +kernel
    rw [ha]
    exact (canonical20309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 3) (sourceB1255 + difference 3 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 3) (sourceB1255 + difference 3 5) sourceC1255) = raw20305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20305; decide +kernel
    rw [ha]
    exact (canonical20305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 4) (sourceB1255 + difference 4 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 4) (sourceB1255 + difference 4 5) sourceC1255) = raw20310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20310; decide +kernel
    rw [ha]
    exact (canonical20310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 5) (sourceB1255 + difference 5 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 5) (sourceB1255 + difference 5 5) sourceC1255) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1255 + sourceB1255) sourceC1255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1255 + sourceB1255) sourceC1255) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1255 sourceB1255 sourceC1255 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1255 sourceB1255 sourceC1255
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1255, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 0) (sourceB1256 + difference 0 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 0) (sourceB1256 + difference 0 0) sourceC1256) = raw19503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw19503; decide +kernel
    rw [ha]
    exact (canonical19503 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 1) (sourceB1256 + difference 1 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 1) (sourceB1256 + difference 1 0) sourceC1256) = raw20311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20311; decide +kernel
    rw [ha]
    exact (canonical20311 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 2) (sourceB1256 + difference 2 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 2) (sourceB1256 + difference 2 0) sourceC1256) = raw20312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20312; decide +kernel
    rw [ha]
    exact (canonical20312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 3) (sourceB1256 + difference 3 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 3) (sourceB1256 + difference 3 0) sourceC1256) = raw20313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20313; decide +kernel
    rw [ha]
    exact (canonical20313 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 4) (sourceB1256 + difference 4 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 4) (sourceB1256 + difference 4 0) sourceC1256) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 5) (sourceB1256 + difference 5 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 5) (sourceB1256 + difference 5 0) sourceC1256) = raw20314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20314; decide +kernel
    rw [ha]
    exact (canonical20314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1256 + sourceB1256) sourceC1256) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1256 + sourceB1256) sourceC1256) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1256 sourceB1256 sourceC1256 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1256 sourceB1256 sourceC1256
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1256, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1257 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 0) (sourceB1257 + difference 0 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 0) (sourceB1257 + difference 0 0) sourceC1257) = raw20315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20315; decide +kernel
    rw [ha]
    exact (canonical20315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 1) (sourceB1257 + difference 1 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 1) (sourceB1257 + difference 1 0) sourceC1257) = raw20316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20316; decide +kernel
    rw [ha]
    exact (canonical20316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 2) (sourceB1257 + difference 2 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 2) (sourceB1257 + difference 2 0) sourceC1257) = raw20317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20317; decide +kernel
    rw [ha]
    exact (canonical20317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 3) (sourceB1257 + difference 3 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 3) (sourceB1257 + difference 3 0) sourceC1257) = raw20318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20318; decide +kernel
    rw [ha]
    exact (canonical20318 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 4) (sourceB1257 + difference 4 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 4) (sourceB1257 + difference 4 0) sourceC1257) = raw20319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20319; decide +kernel
    rw [ha]
    exact (canonical20319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 5) (sourceB1257 + difference 5 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 5) (sourceB1257 + difference 5 0) sourceC1257) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1257 + sourceB1257) sourceC1257) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1257 + sourceB1257) sourceC1257) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA1257 sourceB1257 sourceC1257 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1257 sourceB1257 sourceC1257
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1257, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1072 : Integer.Sparse.reindex keyMap MixedData.row1072 = numericRow1072 := by decide +kernel

theorem numericCheck1072 (x : Master → ℝ) : Integer.Sparse.eval numericRow1072 x =
    (1 : ℝ) * reducedSource1072 x := by
  norm_num [numericRow1072, reducedSource1072, Integer.Sparse.eval, Sparse.eval, nodeValue1619, nodeValue1628, nodeValue1630, nodeValue1756, nodeValue3302, nodeValue4070]

theorem reindexCheck1073 : Integer.Sparse.reindex keyMap MixedData.row1073 = numericRow1073 := by decide +kernel

theorem numericCheck1073 (x : Master → ℝ) : Integer.Sparse.eval numericRow1073 x =
    (1 : ℝ) * reducedSource1073 x := by
  norm_num [numericRow1073, reducedSource1073, Integer.Sparse.eval, Sparse.eval, nodeValue1756, nodeValue2289, nodeValue3302, nodeValue3310, nodeValue4070]

theorem reindexCheck1074 : Integer.Sparse.reindex keyMap MixedData.row1074 = numericRow1074 := by decide +kernel

theorem numericCheck1074 (x : Master → ℝ) : Integer.Sparse.eval numericRow1074 x =
    (1 : ℝ) * reducedSource1074 x := by
  norm_num [numericRow1074, reducedSource1074, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue3291, nodeValue3300, nodeValue3302, nodeValue3310, nodeValue4070]

theorem reindexCheck1075 : Integer.Sparse.reindex keyMap MixedData.row1075 = numericRow1075 := by decide +kernel

theorem numericCheck1075 (x : Master → ℝ) : Integer.Sparse.eval numericRow1075 x =
    (1 : ℝ) * reducedSource1075 x := by
  norm_num [numericRow1075, reducedSource1075, Integer.Sparse.eval, Sparse.eval, nodeValue1630, nodeValue3247, nodeValue3283, nodeValue3300, nodeValue3302, nodeValue4070]

theorem reindexCheck1076 : Integer.Sparse.reindex keyMap MixedData.row1076 = numericRow1076 := by decide +kernel

theorem numericCheck1076 (x : Master → ℝ) : Integer.Sparse.eval numericRow1076 x =
    (1 : ℝ) * reducedSource1076 x := by
  norm_num [numericRow1076, reducedSource1076, Integer.Sparse.eval, Sparse.eval, nodeValue1258, nodeValue2119, nodeValue2130, nodeValue2218, nodeValue2761, nodeValue4082]

theorem reindexCheck1077 : Integer.Sparse.reindex keyMap MixedData.row1077 = numericRow1077 := by decide +kernel

theorem numericCheck1077 (x : Master → ℝ) : Integer.Sparse.eval numericRow1077 x =
    (1 : ℝ) * reducedSource1077 x := by
  norm_num [numericRow1077, reducedSource1077, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue1115, nodeValue1119, nodeValue1131, nodeValue1215, nodeValue2482, nodeValue4092]

theorem reindexCheck1078 : Integer.Sparse.reindex keyMap MixedData.row1078 = numericRow1078 := by decide +kernel

theorem numericCheck1078 (x : Master → ℝ) : Integer.Sparse.eval numericRow1078 x =
    (1 : ℝ) * reducedSource1078 x := by
  norm_num [numericRow1078, reducedSource1078, Integer.Sparse.eval, Sparse.eval, nodeValue626, nodeValue1131, nodeValue1148, nodeValue1215, nodeValue1236, nodeValue1242, nodeValue4092]

theorem reindexCheck1079 : Integer.Sparse.reindex keyMap MixedData.row1079 = numericRow1079 := by decide +kernel

theorem numericCheck1079 (x : Master → ℝ) : Integer.Sparse.eval numericRow1079 x =
    (1 : ℝ) * reducedSource1079 x := by
  norm_num [numericRow1079, reducedSource1079, Integer.Sparse.eval, Sparse.eval, nodeValue630, nodeValue1136, nodeValue1150, nodeValue1217, nodeValue1240, nodeValue4091]

theorem reindexCheck1080 : Integer.Sparse.reindex keyMap MixedData.row1080 = numericRow1080 := by decide +kernel

theorem numericCheck1080 (x : Master → ℝ) : Integer.Sparse.eval numericRow1080 x =
    (1 : ℝ) * reducedSource1080 x := by
  norm_num [numericRow1080, reducedSource1080, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue1118, nodeValue1120, nodeValue1136, nodeValue1217, nodeValue2485, nodeValue4091]

theorem reindexCheck1081 : Integer.Sparse.reindex keyMap MixedData.row1081 = numericRow1081 := by decide +kernel

theorem numericCheck1081 (x : Master → ℝ) : Integer.Sparse.eval numericRow1081 x =
    (1 : ℝ) * reducedSource1081 x := by
  norm_num [numericRow1081, reducedSource1081, Integer.Sparse.eval, Sparse.eval, nodeValue1613, nodeValue1617, nodeValue1619, nodeValue1624, nodeValue1750, nodeValue3291, nodeValue4070]

theorem reindexCheck1082 : Integer.Sparse.reindex keyMap MixedData.row1082 = numericRow1082 := by decide +kernel

theorem numericCheck1082 (x : Master → ℝ) : Integer.Sparse.eval numericRow1082 x =
    (1 : ℝ) * reducedSource1082 x := by
  norm_num [numericRow1082, reducedSource1082, Integer.Sparse.eval, Sparse.eval, nodeValue1596, nodeValue1599, nodeValue1604, nodeValue1617, nodeValue1725, nodeValue3291, nodeValue4070]

theorem reindexCheck1083 : Integer.Sparse.reindex keyMap MixedData.row1083 = numericRow1083 := by decide +kernel

theorem numericCheck1083 (x : Master → ℝ) : Integer.Sparse.eval numericRow1083 x =
    (1 : ℝ) * reducedSource1083 x := by
  norm_num [numericRow1083, reducedSource1083, Integer.Sparse.eval, Sparse.eval, nodeValue1750, nodeValue2226, nodeValue3291, nodeValue3300, nodeValue3310, nodeValue4070]

theorem reindexCheck1084 : Integer.Sparse.reindex keyMap MixedData.row1084 = numericRow1084 := by decide +kernel

theorem numericCheck1084 (x : Master → ℝ) : Integer.Sparse.eval numericRow1084 x =
    (1 : ℝ) * reducedSource1084 x := by
  norm_num [numericRow1084, reducedSource1084, Integer.Sparse.eval, Sparse.eval, nodeValue1617, nodeValue3242, nodeValue3279, nodeValue3291, nodeValue3300, nodeValue4070]

theorem reindexCheck1085 : Integer.Sparse.reindex keyMap MixedData.row1085 = numericRow1085 := by decide +kernel

theorem numericCheck1085 (x : Master → ℝ) : Integer.Sparse.eval numericRow1085 x =
    (1 : ℝ) * reducedSource1085 x := by
  norm_num [numericRow1085, reducedSource1085, Integer.Sparse.eval, Sparse.eval, nodeValue1599, nodeValue1995, nodeValue2005, nodeValue2045, nodeValue2226, nodeValue3291, nodeValue4070]

theorem reindexCheck1086 : Integer.Sparse.reindex keyMap MixedData.row1086 = numericRow1086 := by decide +kernel

theorem numericCheck1086 (x : Master → ℝ) : Integer.Sparse.eval numericRow1086 x =
    (1 : ℝ) * reducedSource1086 x := by
  norm_num [numericRow1086, reducedSource1086, Integer.Sparse.eval, Sparse.eval, nodeValue1211, nodeValue2070, nodeValue2079, nodeValue2087, nodeValue2193, nodeValue2719, nodeValue4080]

theorem reindexCheck1087 : Integer.Sparse.reindex keyMap MixedData.row1087 = numericRow1087 := by decide +kernel

theorem numericCheck1087 (x : Master → ℝ) : Integer.Sparse.eval numericRow1087 x =
    (1 : ℝ) * reducedSource1087 x := by
  norm_num [numericRow1087, reducedSource1087, Integer.Sparse.eval, Sparse.eval, nodeValue1181, nodeValue2385, nodeValue2453, nodeValue2492, nodeValue2664, nodeValue2672, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1072 (mixedVector B) = 0 := by
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1241, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1619, h1628, h1630, h1756, h3302, h4070, reducedSource1072] using sourceEq1241 B hB

theorem rowSound1072 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1072 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1072, numericCheck1072, reducedZero1072 B hB hF, mul_zero]

theorem reducedZero1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1073 (mixedVector B) = 0 := by
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1242, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1756, h2289, h3302, h3310, h4070, reducedSource1073] using sourceEq1242 B hB

theorem rowSound1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1073 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1073, numericCheck1073, reducedZero1073 B hB hF, mul_zero]

theorem reducedZero1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1074 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1243, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h3291, h3300, h3302, h3310, h4070, reducedSource1074] using sourceEq1243 B hB

theorem rowSound1074 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1074 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1074, numericCheck1074, reducedZero1074 B hB hF, mul_zero]

theorem reducedZero1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1075 (mixedVector B) = 0 := by
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3283 : mixedVector B (Sum.inr 3283) = Sparse.eval nodeValue3283 (mixedVector B) := by
    change mixedMoment B node3283 node3283Labels = _
    exact sound3283 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1244, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1630, h3247, h3283, h3300, h3302, h4070, reducedSource1075] using sourceEq1244 B hB

theorem rowSound1075 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1075 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1075, numericCheck1075, reducedZero1075 B hB hF, mul_zero]

theorem reducedZero1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1076 (mixedVector B) = 0 := by
  have h1258 : mixedVector B (Sum.inr 1258) = Sparse.eval nodeValue1258 (mixedVector B) := by
    change mixedMoment B node1258 node1258Labels = _
    exact sound1258 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1246, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1258, h2119, h2130, h2218, h2761, h4082, reducedSource1076] using sourceEq1246 B hB

theorem rowSound1076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1076 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1076, numericCheck1076, reducedZero1076 B hB hF, mul_zero]

theorem reducedZero1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1077 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h1115 : mixedVector B (Sum.inr 1115) = Sparse.eval nodeValue1115 (mixedVector B) := by
    change mixedMoment B node1115 node1115Labels = _
    exact sound1115 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1247, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h1115, h1119, h1131, h1215, h2482, h4092, reducedSource1077] using sourceEq1247 B hB

theorem rowSound1077 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1077 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1077, numericCheck1077, reducedZero1077 B hB hF, mul_zero]

theorem reducedZero1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1078 (mixedVector B) = 0 := by
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1248, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h626, h1131, h1148, h1215, h1236, h1242, h4092, reducedSource1078] using sourceEq1248 B hB

theorem rowSound1078 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1078 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1078, numericCheck1078, reducedZero1078 B hB hF, mul_zero]

theorem reducedZero1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1079 (mixedVector B) = 0 := by
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1249, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h630, h1136, h1150, h1217, h1240, h4091, reducedSource1079] using sourceEq1249 B hB

theorem rowSound1079 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1079 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1079, numericCheck1079, reducedZero1079 B hB hF, mul_zero]

theorem reducedZero1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1080 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1250, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h1118, h1120, h1136, h1217, h2485, h4091, reducedSource1080] using sourceEq1250 B hB

theorem rowSound1080 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1080 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1080, numericCheck1080, reducedZero1080 B hB hF, mul_zero]

theorem reducedZero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1081 (mixedVector B) = 0 := by
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1251, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1613, h1617, h1619, h1624, h1750, h3291, h4070, reducedSource1081] using sourceEq1251 B hB

theorem rowSound1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1081 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1081, numericCheck1081, reducedZero1081 B hB hF, mul_zero]

theorem reducedZero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1082 (mixedVector B) = 0 := by
  have h1596 : mixedVector B (Sum.inr 1596) = Sparse.eval nodeValue1596 (mixedVector B) := by
    change mixedMoment B node1596 node1596Labels = _
    exact sound1596 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1604 : mixedVector B (Sum.inr 1604) = Sparse.eval nodeValue1604 (mixedVector B) := by
    change mixedMoment B node1604 node1604Labels = _
    exact sound1604 B hB hF
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1252, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1596, h1599, h1604, h1617, h1725, h3291, h4070, reducedSource1082] using sourceEq1252 B hB

theorem rowSound1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1082 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1082, numericCheck1082, reducedZero1082 B hB hF, mul_zero]

theorem reducedZero1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1083 (mixedVector B) = 0 := by
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1253, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1750, h2226, h3291, h3300, h3310, h4070, reducedSource1083] using sourceEq1253 B hB

theorem rowSound1083 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1083 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1083, numericCheck1083, reducedZero1083 B hB hF, mul_zero]

theorem reducedZero1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1084 (mixedVector B) = 0 := by
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1254, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1617, h3242, h3279, h3291, h3300, h4070, reducedSource1084] using sourceEq1254 B hB

theorem rowSound1084 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1084 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1084, numericCheck1084, reducedZero1084 B hB hF, mul_zero]

theorem reducedZero1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1085 (mixedVector B) = 0 := by
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1995 : mixedVector B (Sum.inr 1995) = Sparse.eval nodeValue1995 (mixedVector B) := by
    change mixedMoment B node1995 node1995Labels = _
    exact sound1995 B hB hF
  have h2005 : mixedVector B (Sum.inr 2005) = Sparse.eval nodeValue2005 (mixedVector B) := by
    change mixedMoment B node2005 node2005Labels = _
    exact sound2005 B hB hF
  have h2045 : mixedVector B (Sum.inr 2045) = Sparse.eval nodeValue2045 (mixedVector B) := by
    change mixedMoment B node2045 node2045Labels = _
    exact sound2045 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1255, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1599, h1995, h2005, h2045, h2226, h3291, h4070, reducedSource1085] using sourceEq1255 B hB

theorem rowSound1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1085 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1085, numericCheck1085, reducedZero1085 B hB hF, mul_zero]

theorem reducedZero1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1086 (mixedVector B) = 0 := by
  have h1211 : mixedVector B (Sum.inr 1211) = Sparse.eval nodeValue1211 (mixedVector B) := by
    change mixedMoment B node1211 node1211Labels = _
    exact sound1211 B hB hF
  have h2070 : mixedVector B (Sum.inr 2070) = Sparse.eval nodeValue2070 (mixedVector B) := by
    change mixedMoment B node2070 node2070Labels = _
    exact sound2070 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1256, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1211, h2070, h2079, h2087, h2193, h2719, h4080, reducedSource1086] using sourceEq1256 B hB

theorem rowSound1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1086 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1086, numericCheck1086, reducedZero1086 B hB hF, mul_zero]

theorem reducedZero1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1087 (mixedVector B) = 0 := by
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2453 : mixedVector B (Sum.inr 2453) = Sparse.eval nodeValue2453 (mixedVector B) := by
    change mixedMoment B node2453 node2453Labels = _
    exact sound2453 B hB hF
  have h2492 : mixedVector B (Sum.inr 2492) = Sparse.eval nodeValue2492 (mixedVector B) := by
    change mixedMoment B node2492 node2492Labels = _
    exact sound2492 B hB hF
  have h2664 : mixedVector B (Sum.inr 2664) = Sparse.eval nodeValue2664 (mixedVector B) := by
    change mixedMoment B node2664 node2664Labels = _
    exact sound2664 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1257, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1181, h2385, h2453, h2492, h2664, h2672, h4088, reducedSource1087] using sourceEq1257 B hB

theorem rowSound1087 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1087 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1087, numericCheck1087, reducedZero1087 B hB hF, mul_zero]

theorem sourceRowsAt1072 : MixedData.sourceRows (1072 : Fin 2425) =
    MixedData.row1072 := by decide +kernel

theorem sourceRowsAt1073 : MixedData.sourceRows (1073 : Fin 2425) =
    MixedData.row1073 := by decide +kernel

theorem sourceRowsAt1074 : MixedData.sourceRows (1074 : Fin 2425) =
    MixedData.row1074 := by decide +kernel

theorem sourceRowsAt1075 : MixedData.sourceRows (1075 : Fin 2425) =
    MixedData.row1075 := by decide +kernel

theorem sourceRowsAt1076 : MixedData.sourceRows (1076 : Fin 2425) =
    MixedData.row1076 := by decide +kernel

theorem sourceRowsAt1077 : MixedData.sourceRows (1077 : Fin 2425) =
    MixedData.row1077 := by decide +kernel

theorem sourceRowsAt1078 : MixedData.sourceRows (1078 : Fin 2425) =
    MixedData.row1078 := by decide +kernel

theorem sourceRowsAt1079 : MixedData.sourceRows (1079 : Fin 2425) =
    MixedData.row1079 := by decide +kernel

theorem sourceRowsAt1080 : MixedData.sourceRows (1080 : Fin 2425) =
    MixedData.row1080 := by decide +kernel

theorem sourceRowsAt1081 : MixedData.sourceRows (1081 : Fin 2425) =
    MixedData.row1081 := by decide +kernel

theorem sourceRowsAt1082 : MixedData.sourceRows (1082 : Fin 2425) =
    MixedData.row1082 := by decide +kernel

theorem sourceRowsAt1083 : MixedData.sourceRows (1083 : Fin 2425) =
    MixedData.row1083 := by decide +kernel

theorem sourceRowsAt1084 : MixedData.sourceRows (1084 : Fin 2425) =
    MixedData.row1084 := by decide +kernel

theorem sourceRowsAt1085 : MixedData.sourceRows (1085 : Fin 2425) =
    MixedData.row1085 := by decide +kernel

theorem sourceRowsAt1086 : MixedData.sourceRows (1086 : Fin 2425) =
    MixedData.row1086 := by decide +kernel

theorem sourceRowsAt1087 : MixedData.sourceRows (1087 : Fin 2425) =
    MixedData.row1087 := by decide +kernel

theorem chunkSound67_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 67) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1072 ∨ k.val = 1073 ∨ k.val = 1074 ∨ k.val = 1075 ∨ k.val = 1076 ∨ k.val = 1077 ∨ k.val = 1078 ∨ k.val = 1079 ∨ k.val = 1080 ∨ k.val = 1081 ∨ k.val = 1082 ∨ k.val = 1083 ∨ k.val = 1084 ∨ k.val = 1085 ∨ k.val = 1086 ∨ k.val = 1087 := by omega
  rcases heq with h1072 | h1073 | h1074 | h1075 | h1076 | h1077 | h1078 | h1079 | h1080 | h1081 | h1082 | h1083 | h1084 | h1085 | h1086 | h1087
  · have he : k = (1072 : Fin 2425) := Fin.ext h1072
    subst k
    rw [sourceRowsAt1072]
    exact rowSound1072 B hB hF
  · have he : k = (1073 : Fin 2425) := Fin.ext h1073
    subst k
    rw [sourceRowsAt1073]
    exact rowSound1073 B hB hF
  · have he : k = (1074 : Fin 2425) := Fin.ext h1074
    subst k
    rw [sourceRowsAt1074]
    exact rowSound1074 B hB hF
  · have he : k = (1075 : Fin 2425) := Fin.ext h1075
    subst k
    rw [sourceRowsAt1075]
    exact rowSound1075 B hB hF
  · have he : k = (1076 : Fin 2425) := Fin.ext h1076
    subst k
    rw [sourceRowsAt1076]
    exact rowSound1076 B hB hF
  · have he : k = (1077 : Fin 2425) := Fin.ext h1077
    subst k
    rw [sourceRowsAt1077]
    exact rowSound1077 B hB hF
  · have he : k = (1078 : Fin 2425) := Fin.ext h1078
    subst k
    rw [sourceRowsAt1078]
    exact rowSound1078 B hB hF
  · have he : k = (1079 : Fin 2425) := Fin.ext h1079
    subst k
    rw [sourceRowsAt1079]
    exact rowSound1079 B hB hF
  · have he : k = (1080 : Fin 2425) := Fin.ext h1080
    subst k
    rw [sourceRowsAt1080]
    exact rowSound1080 B hB hF
  · have he : k = (1081 : Fin 2425) := Fin.ext h1081
    subst k
    rw [sourceRowsAt1081]
    exact rowSound1081 B hB hF
  · have he : k = (1082 : Fin 2425) := Fin.ext h1082
    subst k
    rw [sourceRowsAt1082]
    exact rowSound1082 B hB hF
  · have he : k = (1083 : Fin 2425) := Fin.ext h1083
    subst k
    rw [sourceRowsAt1083]
    exact rowSound1083 B hB hF
  · have he : k = (1084 : Fin 2425) := Fin.ext h1084
    subst k
    rw [sourceRowsAt1084]
    exact rowSound1084 B hB hF
  · have he : k = (1085 : Fin 2425) := Fin.ext h1085
    subst k
    rw [sourceRowsAt1085]
    exact rowSound1085 B hB hF
  · have he : k = (1086 : Fin 2425) := Fin.ext h1086
    subst k
    rw [sourceRowsAt1086]
    exact rowSound1086 B hB hF
  · have he : k = (1087 : Fin 2425) := Fin.ext h1087
    subst k
    rw [sourceRowsAt1087]
    exact rowSound1087 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e_oai
