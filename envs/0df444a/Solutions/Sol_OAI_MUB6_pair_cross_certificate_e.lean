-- Prove2me | solution 1 for OAI.MUB6.pair_cross_certificate_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:43:29.258188+00:00
-- url     : https://prove2.me/submissions/c2fcf7e2-6a2a-44b0-b6db-5e23b6727902

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E154
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_targetZero0_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm11_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm12_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm13_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm14_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm16_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm17_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm18_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm19_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm21_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm22_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm23_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm24_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm25_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm6_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm7_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm8_e
import Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm9_e

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
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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

theorem sum_split_embedding (e : A ↪ B) (f : B → V) :
    (∑ b, f b) = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b := by
  classical
  let E : A ⊕ {b // b ∉ Set.range e} ≃ B :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range e))
  have h := E.sum_comp f
  simpa [E, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.sumCongr_apply] using h.symm

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

theorem sum_samples_split {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin p ↪ B, ∑ b, f e b) =
      (∑ e : Fin p ↪ B, ∑ j, f e (e j)) +
      ∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0) := by
  classical
  calc
    _ = ∑ e : Fin p ↪ B,
        ((∑ j, f e (e j)) + ∑ b : {b // b ∉ Set.range e}, f e b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_split_embedding e (f e)
    _ = _ := by rw [Finset.sum_add_distrib, sum_injective_extension]

theorem sum_contraction {p : ℕ} (f : (Fin p ↪ B) → B → V)
    (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin p, ∑ e : Fin p ↪ B, f e (e j)) +
      (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) = 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_samples_split]
  simp [h]

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

/-- The normalized counting identity used for an order-one contraction.
At most n rows are sampled; the saturated boundary case is separate. -/
theorem average_contraction {p n : ℕ} (hp : p < n)
    (f : (Fin p ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    ((n - p : ℕ) : ℝ) *
      average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e) (e 0)) +
      (∑ j : Fin p, average (fun e : Fin p ↪ Fin n => f e (e j))) = 0 := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hc : ((n - p : ℕ) : ℝ) * (Fintype.card (Fin (p + 1) ↪ Fin n) : ℝ)⁻¹ =
      (Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ := by
    rw [embedding_succ_card, Nat.cast_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hs := sum_contraction f h
  simp only [average]
  rw [← mul_assoc, hc, ← Finset.mul_sum, ← mul_add]
  rw [add_comm] at hs
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

/-- A uniform injection of all six row indices is a uniform permutation.
This identifies the general partition theorem with the paper's pair average. -/
theorem averagedRowProducts_eq_pairAverage {n : ℕ} (H : CMatrix)
    (A : Matrix Coord (Fin n) ℤ) :
    averagedRowProducts H A =
      pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) := by
  let f : Equiv.Perm Coord → ℝ := fun π =>
    ((∏ j, g (fun i k => H (π i) k) (fun i => A i j)).re +
      (∏ j, g (fun i k => H k (π i)) (fun i => A i j)).re) / 2
  calc
    averagedRowProducts H A =
        average (f ∘ Equiv.embeddingEquivOfFinite Coord) := by rfl
    _ = average f := average_equiv (Equiv.embeddingEquivOfFinite Coord) f
    _ = _ := rfl

theorem pairAverage_products_partition {n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix Coord (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  rw [← averagedRowProducts_eq_pairAverage H A]
  exact averagedRowProducts_partition hH A F cover

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Terms
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

private theorem charge0_0 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) = pairW := by decide +kernel

private theorem charge0_1 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) = -pairW := by decide +kernel

theorem termPolynomial0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term0 = (3 : ℂ) * ((g H pairW) * (conj (g H pairW))) := by
  have hc : (term0.coefficient : ℂ) = (3 : ℂ) := by norm_num [term0]
  change (term0.coefficient : ℂ) * (∏ j : Fin 2, g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) * 1)) = _
  rw [charge0_0, charge0_1]
  simp only [g_neg hH]
  ring

private theorem charge1_0 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge1_1 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 0) := by decide +kernel

private theorem charge1_2 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term1 = (-6 : ℂ) * ((g H pairW) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term1.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term1]
  change (term1.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge1_0, charge1_1, charge1_2]
  simp only [g_neg hH]
  ring

private theorem charge2_0 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge2_1 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 1) := by decide +kernel

private theorem charge2_2 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term2 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term2.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term2]
  change (term2.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge2_0, charge2_1, charge2_2]
  simp only [g_neg hH]
  ring

private theorem charge3_0 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge3_1 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 2) := by decide +kernel

private theorem charge3_2 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term3 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term3.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term3]
  change (term3.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge3_0, charge3_1, charge3_2]
  simp only [g_neg hH]
  ring

private theorem charge4_0 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge4_1 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 3) := by decide +kernel

private theorem charge4_2 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term4 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term4.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term4]
  change (term4.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge4_0, charge4_1, charge4_2]
  simp only [g_neg hH]
  ring

private theorem charge5_0 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 0) := by decide +kernel

private theorem charge5_1 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 0) := by decide +kernel

private theorem charge5_2 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term5 = (-6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H pairW))) := by
  have hc : (term5.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term5]
  change (term5.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge5_0, charge5_1, charge5_2]
  simp only [g_neg hH]
  ring

private theorem charge6_0 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge6_1 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge6_2 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge6_3 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term6 = (12 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term6.coefficient : ℂ) = (12 : ℂ) := by norm_num [term6]
  change (term6.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (12 : ℂ) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge6_0, charge6_1, charge6_2, charge6_3]
  simp only [g_neg hH]
  ring

private theorem charge7_0 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge7_1 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge7_2 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge7_3 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term7 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term7.coefficient : ℂ) = (6 : ℂ) := by norm_num [term7]
  change (term7.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge7_0, charge7_1, charge7_2, charge7_3]
  simp only [g_neg hH]
  ring

private theorem charge8_0 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge8_1 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge8_2 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge8_3 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term8 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term8.coefficient : ℂ) = (6 : ℂ) := by norm_num [term8]
  change (term8.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge8_0, charge8_1, charge8_2, charge8_3]
  simp only [g_neg hH]
  ring

private theorem charge9_0 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge9_1 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge9_2 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge9_3 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term9 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term9.coefficient : ℂ) = (6 : ℂ) := by norm_num [term9]
  change (term9.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge9_0, charge9_1, charge9_2, charge9_3]
  simp only [g_neg hH]
  ring

private theorem charge10_0 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 1) := by decide +kernel

private theorem charge10_1 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 1) := by decide +kernel

private theorem charge10_2 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term10 = (-3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H pairW))) := by
  have hc : (term10.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term10]
  change (term10.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge10_0, charge10_1, charge10_2]
  simp only [g_neg hH]
  ring

private theorem charge11_0 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge11_1 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge11_2 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge11_3 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term11 = (6 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term11.coefficient : ℂ) = (6 : ℂ) := by norm_num [term11]
  change (term11.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge11_0, charge11_1, charge11_2, charge11_3]
  simp only [g_neg hH]
  ring

private theorem charge12_0 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge12_1 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge12_2 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge12_3 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term12 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term12.coefficient : ℂ) = (3 : ℂ) := by norm_num [term12]
  change (term12.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge12_0, charge12_1, charge12_2, charge12_3]
  simp only [g_neg hH]
  ring

private theorem charge13_0 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge13_1 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge13_2 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge13_3 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term13 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term13.coefficient : ℂ) = (3 : ℂ) := by norm_num [term13]
  change (term13.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge13_0, charge13_1, charge13_2, charge13_3]
  simp only [g_neg hH]
  ring

private theorem charge14_0 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge14_1 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge14_2 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge14_3 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term14 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term14.coefficient : ℂ) = (3 : ℂ) := by norm_num [term14]
  change (term14.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge14_0, charge14_1, charge14_2, charge14_3]
  simp only [g_neg hH]
  ring

private theorem charge15_0 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 2) := by decide +kernel

private theorem charge15_1 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 2) := by decide +kernel

private theorem charge15_2 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term15 = (-3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H pairW))) := by
  have hc : (term15.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term15]
  change (term15.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge15_0, charge15_1, charge15_2]
  simp only [g_neg hH]
  ring

private theorem charge16_0 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge16_1 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge16_2 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge16_3 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term16 = (6 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term16.coefficient : ℂ) = (6 : ℂ) := by norm_num [term16]
  change (term16.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge16_0, charge16_1, charge16_2, charge16_3]
  simp only [g_neg hH]
  ring

private theorem charge17_0 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge17_1 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge17_2 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge17_3 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term17 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term17.coefficient : ℂ) = (3 : ℂ) := by norm_num [term17]
  change (term17.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge17_0, charge17_1, charge17_2, charge17_3]
  simp only [g_neg hH]
  ring

private theorem charge18_0 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge18_1 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge18_2 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge18_3 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term18 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term18.coefficient : ℂ) = (3 : ℂ) := by norm_num [term18]
  change (term18.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge18_0, charge18_1, charge18_2, charge18_3]
  simp only [g_neg hH]
  ring

private theorem charge19_0 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge19_1 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge19_2 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge19_3 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term19 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term19.coefficient : ℂ) = (3 : ℂ) := by norm_num [term19]
  change (term19.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge19_0, charge19_1, charge19_2, charge19_3]
  simp only [g_neg hH]
  ring

private theorem charge20_0 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 3) := by decide +kernel

private theorem charge20_1 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 3) := by decide +kernel

private theorem charge20_2 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term20 = (-3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H pairW))) := by
  have hc : (term20.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term20]
  change (term20.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge20_0, charge20_1, charge20_2]
  simp only [g_neg hH]
  ring

private theorem charge21_0 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge21_1 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge21_2 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge21_3 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term21 = (6 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term21.coefficient : ℂ) = (6 : ℂ) := by norm_num [term21]
  change (term21.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge21_0, charge21_1, charge21_2, charge21_3]
  simp only [g_neg hH]
  ring

private theorem charge22_0 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge22_1 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge22_2 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge22_3 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term22 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term22.coefficient : ℂ) = (3 : ℂ) := by norm_num [term22]
  change (term22.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge22_0, charge22_1, charge22_2, charge22_3]
  simp only [g_neg hH]
  ring

private theorem charge23_0 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge23_1 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge23_2 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge23_3 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term23 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term23.coefficient : ℂ) = (3 : ℂ) := by norm_num [term23]
  change (term23.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge23_0, charge23_1, charge23_2, charge23_3]
  simp only [g_neg hH]
  ring

private theorem charge24_0 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge24_1 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge24_2 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge24_3 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term24 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term24.coefficient : ℂ) = (3 : ℂ) := by norm_num [term24]
  change (term24.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge24_0, charge24_1, charge24_2, charge24_3]
  simp only [g_neg hH]
  ring

private theorem charge25_0 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = alpha := by decide +kernel

private theorem charge25_1 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = qCross := by decide +kernel

private theorem charge25_2 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -alpha := by decide +kernel

private theorem charge25_3 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -qCross := by decide +kernel

theorem termPolynomial25 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term25 = (1 : ℂ) * ((g H alpha) * (g H qCross) * (conj (g H alpha)) * (conj (g H qCross))) := by
  have hc : (term25.coefficient : ℂ) = (1 : ℂ) := by norm_num [term25]
  change (term25.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (1 : ℂ) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge25_0, charge25_1, charge25_2, charge25_3]
  simp only [g_neg hH]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Grid
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem pairSummand_sum (H : CMatrix) : (∑ r, pairSummand H r) = pairL H := by
  simp [pairSummand, pairL, pairCoefficient, Fin.sum_univ_succ]

private theorem grid0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 0) = 3 * (pairSummand H 0 * conj (pairSummand H 0)) := by
  change termPolynomial H term0 = _
  rw [termPolynomial0 hH]
  simp [pairSummand, map_neg]

private theorem grid1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 1) = 3 * (pairSummand H 0 * conj (pairSummand H 1)) := by
  change termPolynomial H term1 = _
  rw [termPolynomial1 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 2) = 3 * (pairSummand H 0 * conj (pairSummand H 2)) := by
  change termPolynomial H term2 = _
  rw [termPolynomial2 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 3) = 3 * (pairSummand H 0 * conj (pairSummand H 3)) := by
  change termPolynomial H term3 = _
  rw [termPolynomial3 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 4) = 3 * (pairSummand H 0 * conj (pairSummand H 4)) := by
  change termPolynomial H term4 = _
  rw [termPolynomial4 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 0) = 3 * (pairSummand H 1 * conj (pairSummand H 0)) := by
  change termPolynomial H term5 = _
  rw [termPolynomial5 hH]
  simp [pairSummand, map_neg]
  ring

private theorem grid6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 1) = 3 * (pairSummand H 1 * conj (pairSummand H 1)) := by
  change termPolynomial H term6 = _
  rw [termPolynomial6 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 2) = 3 * (pairSummand H 1 * conj (pairSummand H 2)) := by
  change termPolynomial H term7 = _
  rw [termPolynomial7 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 3) = 3 * (pairSummand H 1 * conj (pairSummand H 3)) := by
  change termPolynomial H term8 = _
  rw [termPolynomial8 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 4) = 3 * (pairSummand H 1 * conj (pairSummand H 4)) := by
  change termPolynomial H term9 = _
  rw [termPolynomial9 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 0) = 3 * (pairSummand H 2 * conj (pairSummand H 0)) := by
  change termPolynomial H term10 = _
  rw [termPolynomial10 hH]
  simp [pairSummand, map_neg]

private theorem grid11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 1) = 3 * (pairSummand H 2 * conj (pairSummand H 1)) := by
  change termPolynomial H term11 = _
  rw [termPolynomial11 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 2) = 3 * (pairSummand H 2 * conj (pairSummand H 2)) := by
  change termPolynomial H term12 = _
  rw [termPolynomial12 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 3) = 3 * (pairSummand H 2 * conj (pairSummand H 3)) := by
  change termPolynomial H term13 = _
  rw [termPolynomial13 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 4) = 3 * (pairSummand H 2 * conj (pairSummand H 4)) := by
  change termPolynomial H term14 = _
  rw [termPolynomial14 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 0) = 3 * (pairSummand H 3 * conj (pairSummand H 0)) := by
  change termPolynomial H term15 = _
  rw [termPolynomial15 hH]
  simp [pairSummand, map_neg]

private theorem grid16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 1) = 3 * (pairSummand H 3 * conj (pairSummand H 1)) := by
  change termPolynomial H term16 = _
  rw [termPolynomial16 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 2) = 3 * (pairSummand H 3 * conj (pairSummand H 2)) := by
  change termPolynomial H term17 = _
  rw [termPolynomial17 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 3) = 3 * (pairSummand H 3 * conj (pairSummand H 3)) := by
  change termPolynomial H term18 = _
  rw [termPolynomial18 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 4) = 3 * (pairSummand H 3 * conj (pairSummand H 4)) := by
  change termPolynomial H term19 = _
  rw [termPolynomial19 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 0) = 3 * (pairSummand H 4 * conj (pairSummand H 0)) := by
  change termPolynomial H term20 = _
  rw [termPolynomial20 hH]
  simp [pairSummand, map_neg]

private theorem grid21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 1) = 3 * (pairSummand H 4 * conj (pairSummand H 1)) := by
  change termPolynomial H term21 = _
  rw [termPolynomial21 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 2) = 3 * (pairSummand H 4 * conj (pairSummand H 2)) := by
  change termPolynomial H term22 = _
  rw [termPolynomial22 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 3) = 3 * (pairSummand H 4 * conj (pairSummand H 3)) := by
  change termPolynomial H term23 = _
  rw [termPolynomial23 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 4) = 3 * (pairSummand H 4 * conj (pairSummand H 4)) := by
  change termPolynomial H term24 = _
  rw [termPolynomial24 hH]
  simp [pairSummand, map_mul]
  ring

theorem termGrid_polynomial {H : CMatrix} (hH : IsHadamard H) (r s : Fin 5) :
    termPolynomial H (termGrid r s) = 3 * (pairSummand H r * conj (pairSummand H s)) := by
  fin_cases r
  · fin_cases s
    · exact grid0 hH
    · exact grid1 hH
    · exact grid2 hH
    · exact grid3 hH
    · exact grid4 hH
  · fin_cases s
    · exact grid5 hH
    · exact grid6 hH
    · exact grid7 hH
    · exact grid8 hH
    · exact grid9 hH
  · fin_cases s
    · exact grid10 hH
    · exact grid11 hH
    · exact grid12 hH
    · exact grid13 hH
    · exact grid14 hH
  · fin_cases s
    · exact grid15 hH
    · exact grid16 hH
    · exact grid17 hH
    · exact grid18 hH
    · exact grid19 hH
  · fin_cases s
    · exact grid20 hH
    · exact grid21 hH
    · exact grid22 hH
    · exact grid23 hH
    · exact grid24 hH

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairPolynomial_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem sum_grid_polynomial (x : Fin 5 → ℂ) :
    (∑ r, ∑ s, 3 * (x r * conj (x s))) = 3 * ((∑ r, x r) * conj (∑ s, x s)) := by
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem termGrid_at0 : termGrid 0 0 = term0 := rfl
private theorem termGrid_at1 : termGrid 0 1 = term1 := rfl
private theorem termGrid_at2 : termGrid 0 2 = term2 := rfl
private theorem termGrid_at3 : termGrid 0 3 = term3 := rfl
private theorem termGrid_at4 : termGrid 0 4 = term4 := rfl
private theorem termGrid_at5 : termGrid 1 0 = term5 := rfl
private theorem termGrid_at6 : termGrid 1 1 = term6 := rfl
private theorem termGrid_at7 : termGrid 1 2 = term7 := rfl
private theorem termGrid_at8 : termGrid 1 3 = term8 := rfl
private theorem termGrid_at9 : termGrid 1 4 = term9 := rfl
private theorem termGrid_at10 : termGrid 2 0 = term10 := rfl
private theorem termGrid_at11 : termGrid 2 1 = term11 := rfl
private theorem termGrid_at12 : termGrid 2 2 = term12 := rfl
private theorem termGrid_at13 : termGrid 2 3 = term13 := rfl
private theorem termGrid_at14 : termGrid 2 4 = term14 := rfl
private theorem termGrid_at15 : termGrid 3 0 = term15 := rfl
private theorem termGrid_at16 : termGrid 3 1 = term16 := rfl
private theorem termGrid_at17 : termGrid 3 2 = term17 := rfl
private theorem termGrid_at18 : termGrid 3 3 = term18 := rfl
private theorem termGrid_at19 : termGrid 3 4 = term19 := rfl
private theorem termGrid_at20 : termGrid 4 0 = term20 := rfl
private theorem termGrid_at21 : termGrid 4 1 = term21 := rfl
private theorem termGrid_at22 : termGrid 4 2 = term22 := rfl
private theorem termGrid_at23 : termGrid 4 3 = term23 := rfl
private theorem termGrid_at24 : termGrid 4 4 = term24 := rfl

private theorem terms0_at0 : terms0 0 = term0 := rfl
private theorem terms0_at1 : terms0 1 = term1 := rfl
private theorem terms0_at2 : terms0 2 = term2 := rfl
private theorem terms0_at3 : terms0 3 = term3 := rfl
private theorem terms0_at4 : terms0 4 = term4 := rfl
private theorem terms0_at5 : terms0 5 = term5 := rfl
private theorem terms0_at6 : terms0 6 = term6 := rfl
private theorem terms0_at7 : terms0 7 = term7 := rfl
private theorem terms0_at8 : terms0 8 = term8 := rfl
private theorem terms0_at9 : terms0 9 = term9 := rfl
private theorem terms0_at10 : terms0 10 = term10 := rfl
private theorem terms0_at11 : terms0 11 = term11 := rfl
private theorem terms0_at12 : terms0 12 = term12 := rfl
private theorem terms0_at13 : terms0 13 = term13 := rfl
private theorem terms0_at14 : terms0 14 = term14 := rfl
private theorem terms0_at15 : terms0 15 = term15 := rfl
private theorem terms0_at16 : terms0 16 = term16 := rfl
private theorem terms0_at17 : terms0 17 = term17 := rfl
private theorem terms0_at18 : terms0 18 = term18 := rfl
private theorem terms0_at19 : terms0 19 = term19 := rfl
private theorem terms0_at20 : terms0 20 = term20 := rfl
private theorem terms0_at21 : terms0 21 = term21 := rfl
private theorem terms0_at22 : terms0 22 = term22 := rfl
private theorem terms0_at23 : terms0 23 = term23 := rfl
private theorem terms0_at24 : terms0 24 = term24 := rfl
private theorem terms0_at25 : terms0 25 = term25 := rfl
theorem sum_terms0 (F : Term → ℂ) :
    (∑ i : Fin 26, F (terms0 i)) = (∑ r : Fin 5, ∑ s : Fin 5, F (termGrid r s)) + F term25 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms0 0) + (F (terms0 1) + (F (terms0 2) + (F (terms0 3) + (F (terms0 4) + (F (terms0 5) + (F (terms0 6) + (F (terms0 7) + (F (terms0 8) + (F (terms0 9) + (F (terms0 10) + (F (terms0 11) + (F (terms0 12) + (F (terms0 13) + (F (terms0 14) + (F (terms0 15) + (F (terms0 16) + (F (terms0 17) + (F (terms0 18) + (F (terms0 19) + (F (terms0 20) + (F (terms0 21) + (F (terms0 22) + (F (terms0 23) + (F (terms0 24) + (F (terms0 25) + 0)))))))))))))))))))))))))) = ((F (termGrid 0 0) + (F (termGrid 0 1) + (F (termGrid 0 2) + (F (termGrid 0 3) + (F (termGrid 0 4) + 0))))) + ((F (termGrid 1 0) + (F (termGrid 1 1) + (F (termGrid 1 2) + (F (termGrid 1 3) + (F (termGrid 1 4) + 0))))) + ((F (termGrid 2 0) + (F (termGrid 2 1) + (F (termGrid 2 2) + (F (termGrid 2 3) + (F (termGrid 2 4) + 0))))) + ((F (termGrid 3 0) + (F (termGrid 3 1) + (F (termGrid 3 2) + (F (termGrid 3 3) + (F (termGrid 3 4) + 0))))) + ((F (termGrid 4 0) + (F (termGrid 4 1) + (F (termGrid 4 2) + (F (termGrid 4 3) + (F (termGrid 4 4) + 0))))) + 0))))) + F term25
  simp only [terms0_at0, terms0_at1, terms0_at2, terms0_at3, terms0_at4, terms0_at5, terms0_at6, terms0_at7, terms0_at8, terms0_at9, terms0_at10, terms0_at11, terms0_at12, terms0_at13, terms0_at14, terms0_at15, terms0_at16, terms0_at17, terms0_at18, terms0_at19, terms0_at20, terms0_at21, terms0_at22, terms0_at23, terms0_at24, terms0_at25, termGrid_at0, termGrid_at1, termGrid_at2, termGrid_at3, termGrid_at4, termGrid_at5, termGrid_at6, termGrid_at7, termGrid_at8, termGrid_at9, termGrid_at10, termGrid_at11, termGrid_at12, termGrid_at13, termGrid_at14, termGrid_at15, termGrid_at16, termGrid_at17, termGrid_at18, termGrid_at19, termGrid_at20, termGrid_at21, termGrid_at22, termGrid_at23, termGrid_at24, add_zero, add_assoc]

theorem pair_polynomial0 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, termPolynomial H (terms0 i)) =
      3 * (pairL H * conj (pairL H)) +
        (g H alpha * g H qCross) * conj (g H alpha * g H qCross) := by
  rw [sum_terms0]
  simp_rw [termGrid_polynomial hH]
  rw [sum_grid_polynomial, pairSummand_sum, termPolynomial25 hH]
  simp only [map_mul, one_mul]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairInterpretation
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem pairAverage_add (H : CMatrix) (F G : CMatrix → ℝ) :
    pairAverage H (fun K => F K + G K) = pairAverage H F + pairAverage H G := by
  have h (π : Equiv.Perm Coord) :
      ((F (fun i j => H (π i) j) + G (fun i j => H (π i) j)) +
        (F (fun i j => H j (π i)) + G (fun i j => H j (π i)))) / 2 =
      (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2 +
        (G (fun i j => H (π i) j) + G (fun i j => H j (π i))) / 2 := by ring
  simp only [pairAverage, h, average_add]

theorem pairAverage_mul (H : CMatrix) (c : ℝ) (F : CMatrix → ℝ) :
    pairAverage H (fun K => c * F K) = c * pairAverage H F := by
  unfold pairAverage
  have h (π : Equiv.Perm Coord) :
      (c * F (fun i j => H (π i) j) + c * F (fun i j => H j (π i))) / 2 =
      c * ((F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2) := by ring
  simp_rw [h]
  exact average_mul c _

theorem pairAverage_sum {ι : Type*} [Fintype ι] (H : CMatrix) (F : ι → CMatrix → ℝ) :
    pairAverage H (fun K => ∑ i, F i K) = ∑ i, pairAverage H (F i) := by
  simp only [pairAverage, ← Finset.sum_add_distrib, div_eq_mul_inv,
    Finset.sum_mul, average_sum]

theorem pairAverage_congr_hadamard {H : CMatrix} (hH : IsHadamard H)
    {F G : CMatrix → ℝ} (h : ∀ K, IsHadamard K → F K = G K) :
    pairAverage H F = pairAverage H G := by
  apply average_congr
  intro π
  have h₁ : IsHadamard (fun i j => H (π i) j) := by
    simpa only [Equiv.refl_apply] using hH.permutations π (Equiv.refl Coord)
  have h₂ : IsHadamard (fun i j => H j (π i)) := by
    simpa only [Equiv.refl_apply, Matrix.transpose_apply] using
      hH.transpose.permutations π (Equiv.refl Coord)
  rw [h _ h₁, h _ h₂]

namespace Certificate.PairTargetSemantics

theorem termPolynomial_re (H : CMatrix) (t : Term) :
    (termPolynomial H t).re = (t.coefficient : ℝ) * (∏ j, g H (fun i => t.charges i j)).re := by
  simp [termPolynomial, Complex.mul_re]

theorem pair_real_polynomial0 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, ((terms0 i).coefficient : ℝ) *
      (∏ j, g H (fun k => (terms0 i).charges k j)).re) =
      3 * Complex.normSq (pairL H) + Complex.normSq (g H alpha * g H qCross) := by
  have h := congrArg Complex.re (pair_polynomial0 hH)
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa only [Complex.re_sum, termPolynomial_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem expanded_identity0 {H : CMatrix} (hH : IsHadamard H) :
    expanded0 H = 3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
      pairAverage H (fun K => Complex.normSq (g K alpha * g K qCross)) := by
  calc
    _ = pairAverage H (fun K => ∑ i : Fin 26, ((terms0 i).coefficient : ℝ) *
        (∏ j, g K (fun k => (terms0 i).charges k j)).re) := by
      simp only [pairAverage_sum, pairAverage_mul, expanded0, weightedAverage]
    _ = pairAverage H (fun K => 3 * Complex.normSq (pairL K) +
        Complex.normSq (g K alpha * g K qCross)) :=
      pairAverage_congr_hadamard hH (fun _ hK => pair_real_polynomial0 hK)
    _ = _ := by rw [pairAverage_add, pairAverage_mul]

end Certificate.PairTargetSemantics
end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairTermSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6.Certificate.PairTargetSemantics

private theorem sumterms0_at0 : terms0 0 = term0 := rfl
private theorem sumterms0_at1 : terms0 1 = term1 := rfl
private theorem sumterms0_at2 : terms0 2 = term2 := rfl
private theorem sumterms0_at3 : terms0 3 = term3 := rfl
private theorem sumterms0_at4 : terms0 4 = term4 := rfl
private theorem sumterms0_at5 : terms0 5 = term5 := rfl
private theorem sumterms0_at6 : terms0 6 = term6 := rfl
private theorem sumterms0_at7 : terms0 7 = term7 := rfl
private theorem sumterms0_at8 : terms0 8 = term8 := rfl
private theorem sumterms0_at9 : terms0 9 = term9 := rfl
private theorem sumterms0_at10 : terms0 10 = term10 := rfl
private theorem sumterms0_at11 : terms0 11 = term11 := rfl
private theorem sumterms0_at12 : terms0 12 = term12 := rfl
private theorem sumterms0_at13 : terms0 13 = term13 := rfl
private theorem sumterms0_at14 : terms0 14 = term14 := rfl
private theorem sumterms0_at15 : terms0 15 = term15 := rfl
private theorem sumterms0_at16 : terms0 16 = term16 := rfl
private theorem sumterms0_at17 : terms0 17 = term17 := rfl
private theorem sumterms0_at18 : terms0 18 = term18 := rfl
private theorem sumterms0_at19 : terms0 19 = term19 := rfl
private theorem sumterms0_at20 : terms0 20 = term20 := rfl
private theorem sumterms0_at21 : terms0 21 = term21 := rfl
private theorem sumterms0_at22 : terms0 22 = term22 := rfl
private theorem sumterms0_at23 : terms0 23 = term23 := rfl
private theorem sumterms0_at24 : terms0 24 = term24 := rfl
private theorem sumterms0_at25 : terms0 25 = term25 := rfl
theorem sum_terms0_expand {R : Type*} [AddCommMonoid R] (F : Term → R) :
    (∑ i : Fin 26, F (terms0 i)) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term25 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms0 0) + (F (terms0 1) + (F (terms0 2) + (F (terms0 3) + (F (terms0 4) + (F (terms0 5) + (F (terms0 6) + (F (terms0 7) + (F (terms0 8) + (F (terms0 9) + (F (terms0 10) + (F (terms0 11) + (F (terms0 12) + (F (terms0 13) + (F (terms0 14) + (F (terms0 15) + (F (terms0 16) + (F (terms0 17) + (F (terms0 18) + (F (terms0 19) + (F (terms0 20) + (F (terms0 21) + (F (terms0 22) + (F (terms0 23) + (F (terms0 24) + (F (terms0 25) + 0)))))))))))))))))))))))))) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term25
  simp only [sumterms0_at0, sumterms0_at1, sumterms0_at2, sumterms0_at3, sumterms0_at4, sumterms0_at5, sumterms0_at6, sumterms0_at7, sumterms0_at8, sumterms0_at9, sumterms0_at10, sumterms0_at11, sumterms0_at12, sumterms0_at13, sumterms0_at14, sumterms0_at15, sumterms0_at16, sumterms0_at17, sumterms0_at18, sumterms0_at19, sumterms0_at20, sumterms0_at21, sumterms0_at22, sumterms0_at23, sumterms0_at24, sumterms0_at25, add_zero, add_assoc]

end MUB6.Certificate.PairTargetSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5123 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5123 = injectiveMoment H raw5123step0 := by
      have hz : ∀ j, raw5123 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5123step0 = (fun i j => raw5123 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123 permutation241 hz
    injectiveMoment H raw5123step0 = injectiveMoment H raw5123step1 := by
      have hz : ∀ j, raw5123step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5123step1 = (fun i j => raw5123step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123step0 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5124 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5124 = injectiveMoment H raw5124step0 := by
      have hz : ∀ j, raw5124 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5124step0 = (fun i j => raw5124 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124 permutation241 hz
    injectiveMoment H raw5124step0 = injectiveMoment H raw5124step1 := by
      have hz : ∀ j, raw5124step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5124step1 = (fun i j => raw5124step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124step0 permutation80 hz
    injectiveMoment H raw5124step1 = injectiveMoment H raw5124step2 := by
      have heq : raw5124step2 = (fun i j => raw5124step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5124step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

theorem canonical5127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5127 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5127 = injectiveMoment H raw5127step0 := by
      have hz : ∀ j, raw5127 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw5127step0 = (fun i j => raw5127 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5127 permutation221 hz
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7625 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7625 = injectiveMoment H raw7625step0 := by
      have hz : ∀ j, raw7625 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw7625step0 = (fun i j => raw7625 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7625 permutation221 hz
    injectiveMoment H raw7625step0 = injectiveMoment H raw7625step1 := by
      have heq : raw7625step1 = (fun i j => raw7625step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7625step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7668 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7668 = injectiveMoment H raw7668step0 := by
      have hz : ∀ j, raw7668 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7668step0 = (fun i j => raw7668 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668 permutation241 hz
    injectiveMoment H raw7668step0 = injectiveMoment H raw7668step1 := by
      have hz : ∀ j, raw7668step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7668step1 = (fun i j => raw7668step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668step0 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8160 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8160 = injectiveMoment H raw8160step0 := by
      have heq : raw8160step0 = (fun i j => raw8160 (permutation15 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8160 permutation15 permutation3
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4044 = injectiveMoment H node202 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2726 = injectiveMoment H node167 := by
  rfl

theorem canonical2727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2727 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2727 = injectiveMoment H raw2727step0 := by
      have heq : raw2727step0 = (fun i j => raw2727 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2727 permutation10 permutation3
    _ = injectiveMoment H node167 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2767 = injectiveMoment H node175 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5164 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5164 = injectiveMoment H raw5164step0 := by
      have hz : ∀ j, raw5164 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5164step0 = (fun i j => raw5164 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164 permutation241 hz
    injectiveMoment H raw5164step0 = injectiveMoment H raw5164step1 := by
      have hz : ∀ j, raw5164step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5164step1 = (fun i j => raw5164step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step0 permutation80 hz
    injectiveMoment H raw5164step1 = injectiveMoment H raw5164step2 := by
      have hz : ∀ j, raw5164step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5164step2 = (fun i j => raw5164step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7982 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7982 = injectiveMoment H raw7982step0 := by
      have hz : ∀ j, raw7982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7982step0 = (fun i j => raw7982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982 permutation308 hz
    injectiveMoment H raw7982step0 = injectiveMoment H raw7982step1 := by
      have hz : ∀ j, raw7982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7982step1 = (fun i j => raw7982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step0 permutation128 hz
    injectiveMoment H raw7982step1 = injectiveMoment H raw7982step2 := by
      have hz : ∀ j, raw7982step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7982step2 = (fun i j => raw7982step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step1 permutation27 hz
    injectiveMoment H raw7982step2 = injectiveMoment H raw7982step3 := by
      have hz : ∀ j, raw7982step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7982step3 = (fun i j => raw7982step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step2 permutation7 hz
    injectiveMoment H raw7982step3 = injectiveMoment H raw7982step4 := by
      have hz : ∀ j, raw7982step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7982step4 = (fun i j => raw7982step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step3 permutation2 hz
    injectiveMoment H raw7982step4 = injectiveMoment H raw7982step5 := by
      have hz : ∀ j, raw7982step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7982step5 = (fun i j => raw7982step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step4 permutation0 hz
    injectiveMoment H raw7982step5 = injectiveMoment H raw7982step6 := by
      have hz : ∀ i, raw7982step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7982step6 = (fun i j => raw7982step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7982step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw845 = injectiveMoment H node117 := by
  calc
    injectiveMoment H raw845 = injectiveMoment H raw845step0 := by
      have hz : ∀ j, raw845 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw845step0 = (fun i j => raw845 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw845 permutation221 hz
    _ = injectiveMoment H node117 := by rfl

theorem canonical852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw852 = injectiveMoment H node23 := by
  rfl

theorem canonical853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw853 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw853 = injectiveMoment H raw853step0 := by
      have heq : raw853step0 = (fun i j => raw853 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw853 permutation10 permutation1
    _ = injectiveMoment H node23 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound23 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node23 = Sparse.eval value23 (momentVector H) := by
  have hc : momentVector H 68 = injectiveMoment H node23 := rfl
  simp [value23, Sparse.eval, hc]

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node167 = Sparse.eval value167 (momentVector H) := by
  have hc : momentVector H 126 = injectiveMoment H node167 := rfl
  simp [value167, Sparse.eval, hc]

theorem sound175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node175 = Sparse.eval value175 (momentVector H) := by
  have heq : pivotMatrix175 = (fun u v => node175 (pivotPermutation175 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node175 = injectiveMoment H pivotMatrix175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix175 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix175 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (2 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node175 + (injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value175, value35, value56, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node202 = Sparse.eval value202 (momentVector H) := by
  have hc : momentVector H 24 = injectiveMoment H node202 := rfl
  simp [value202, Sparse.eval, hc]

theorem sound232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node232 = Sparse.eval value232 (momentVector H) := by
  have heq : pivotMatrix232 = (fun u v => node232 (pivotPermutation232 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node232 = injectiveMoment H pivotMatrix232 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix232 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix232 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (0 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (1 : Fin 4) = raw5177 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5177 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (2 : Fin 4) = raw5197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5197 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix232 (3 : Fin 4) = raw5204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5204 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node232 + (injectiveMoment H (mergeFirst pivotMatrix232 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix232 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value232, value11, value26, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5848 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5848 = injectiveMoment H raw5848step0 := by
      have heq : raw5848step0 = raw5848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5848).symm
    injectiveMoment H raw5848step0 = injectiveMoment H raw5848step1 := by
      have heq : raw5848step1 = (fun i j => raw5848step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5848step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5937 = injectiveMoment H node268 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1332 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw1332 = injectiveMoment H raw1332step0 := by
      have heq : raw1332step0 = raw1332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1332).symm
    _ = injectiveMoment H node45 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node117 = Sparse.eval value117 (momentVector H) := by
  have heq : pivotMatrix117 = (fun u v => node117 (pivotPermutation117 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node117 = injectiveMoment H pivotMatrix117 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix117 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix117 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (0 : Fin 4) = raw5116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5116 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (1 : Fin 4) = raw872 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical872 hH).trans (sound25 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (2 : Fin 4) = raw853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical853 hH).trans (sound23 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)) =
      Sparse.eval value23 (momentVector H) := by
    have heq : mergeFirst pivotMatrix117 (3 : Fin 4) = raw852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical852 hH).trans (sound23 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node117 + (injectiveMoment H (mergeFirst pivotMatrix117 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix117 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value117, value23, value25, value45, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node258 = Sparse.eval value258 (momentVector H) := by
  have hc : momentVector H 236 = injectiveMoment H node258 := rfl
  simp [value258, Sparse.eval, hc]

theorem sound268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node268 = Sparse.eval value268 (momentVector H) := by
  have heq : pivotMatrix268 = (fun u v => node268 (pivotPermutation268 u) v) := by apply Matrix.ext; unfold pivotMatrix268 node268 pivotPermutation268; decide +kernel
  have hmoment : injectiveMoment H node268 = injectiveMoment H pivotMatrix268 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix268 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix268 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (0 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix268 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix268 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node268 + (injectiveMoment H (mergeFirst pivotMatrix268 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix268 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value268, value52, value56, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node275 = Sparse.eval value275 (momentVector H) := by
  have hc : momentVector H 30 = injectiveMoment H node275 := rfl
  simp [value275, Sparse.eval, hc]

theorem sound279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node279 = Sparse.eval value279 (momentVector H) := by
  have heq : pivotMatrix279 = (fun u v => node279.transpose (pivotPermutation279 u) v) := by apply Matrix.ext; unfold pivotMatrix279 node279 pivotPermutation279; decide +kernel
  have hmoment : injectiveMoment H node279 = injectiveMoment H pivotMatrix279 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix279 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix279 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (0 : Fin 2) = raw1332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw1332; decide +kernel
    rw [heq]
    exact (canonical1332 hH).trans (sound45 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix279 (1 : Fin 2) = raw5848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix279 raw5848; decide +kernel
    rw [heq]
    exact (canonical5848 hH).trans (sound46 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node279 + (injectiveMoment H (mergeFirst pivotMatrix279 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix279 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value279, value45, value46, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6735 = injectiveMoment H node275 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5857 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5857 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw5857 = injectiveMoment H raw5857step0 := by
      have heq : raw5857step0 = -raw5857 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5857).symm
    injectiveMoment H raw5857step0 = injectiveMoment H raw5857step1 := by
      have heq : raw5857step1 = (fun i j => raw5857step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5857step0 permutation32 permutation3
    _ = injectiveMoment H node167 := by rfl

theorem canonical5864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5864 = injectiveMoment H node258 := by
  rfl

theorem canonical5865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5865 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw5865 = injectiveMoment H raw5865step0 := by
      have heq : raw5865step0 = (fun i j => raw5865 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5865 permutation10 permutation3
    _ = injectiveMoment H node258 := by rfl

theorem canonical5872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5872 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw5872 = injectiveMoment H raw5872step0 := by
      have heq : raw5872step0 = (fun i j => raw5872 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5872 permutation9 permutation5
    _ = injectiveMoment H node175 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound856 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node856 = Sparse.eval value856 (momentVector H) := by
  have heq : pivotMatrix856 = (fun u v => node856 (pivotPermutation856 u) v) := by apply Matrix.ext; unfold pivotMatrix856 node856 pivotPermutation856; decide +kernel
  have hmoment : injectiveMoment H node856 = injectiveMoment H pivotMatrix856 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix856 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix856 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (0 : Fin 4) = raw6735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw6735; decide +kernel
    rw [heq]
    exact (canonical6735 hH).trans (sound275 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (1 : Fin 4) = raw5872 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5872; decide +kernel
    rw [heq]
    exact (canonical5872 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix856 (3 : Fin 4) = raw5864 := by apply Matrix.ext; unfold mergeFirst pivotMatrix856 raw5864; decide +kernel
    rw [heq]
    exact (canonical5864 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node856 + (injectiveMoment H (mergeFirst pivotMatrix856 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix856 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value856, value175, value258, value275, Sparse.eval] at hc ⊢
  linarith

theorem sound858 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node858 = Sparse.eval value858 (momentVector H) := by
  have heq : pivotMatrix858 = (fun u v => node858 (pivotPermutation858 u) v) := by apply Matrix.ext; unfold pivotMatrix858 node858 pivotPermutation858; decide +kernel
  have hmoment : injectiveMoment H node858 = injectiveMoment H pivotMatrix858 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix858 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix858 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (0 : Fin 4) = raw8160 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw8160; decide +kernel
    rw [heq]
    exact (canonical8160 hH).trans (sound279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) =
      Sparse.eval value268 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (1 : Fin 4) = raw5937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5937; decide +kernel
    rw [heq]
    exact (canonical5937 hH).trans (sound268 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (2 : Fin 4) = raw5865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5865; decide +kernel
    rw [heq]
    exact (canonical5865 hH).trans (sound258 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix858 (3 : Fin 4) = raw5857 := by apply Matrix.ext; unfold mergeFirst pivotMatrix858 raw5857; decide +kernel
    rw [heq]
    exact (canonical5857 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node858 + (injectiveMoment H (mergeFirst pivotMatrix858 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix858 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value858, value167, value258, value268, value279, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node545 = Sparse.eval value545 (momentVector H) := by
  have heq : pivotMatrix545 = (fun u v => node545 (pivotPermutation545 u) v) := by apply Matrix.ext; unfold pivotMatrix545 node545 pivotPermutation545; decide +kernel
  have hmoment : injectiveMoment H node545 = injectiveMoment H pivotMatrix545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix545 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix545 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (0 : Fin 4) = raw4044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw4044; decide +kernel
    rw [heq]
    exact (canonical4044 hH).trans (sound202 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (1 : Fin 4) = raw2767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2767; decide +kernel
    rw [heq]
    exact (canonical2767 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (2 : Fin 4) = raw2727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2727; decide +kernel
    rw [heq]
    exact (canonical2727 hH).trans (sound167 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix545 (3 : Fin 4) = raw2726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix545 raw2726; decide +kernel
    rw [heq]
    exact (canonical2726 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node545 + (injectiveMoment H (mergeFirst pivotMatrix545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value545, value167, value175, value202, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem integerMergeCheck0 : integerMerge0 =
    Integer.Sparse.merge integerTerm1 integerTerm2 := by decide +kernel

theorem integerMergeEval0 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge0 x =
      Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck0, Integer.Sparse.eval_merge]

theorem integerMergeCheck1 : integerMerge1 =
    Integer.Sparse.merge integerTerm0 integerMerge0 := by decide +kernel

theorem integerMergeEval1 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge1 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck1, Integer.Sparse.eval_merge]
  rw [integerMergeEval0]
  all_goals ring

theorem integerMergeCheck2 : integerMerge2 =
    Integer.Sparse.merge integerTerm4 integerTerm5 := by decide +kernel

theorem integerMergeEval2 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge2 x =
      Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck2, Integer.Sparse.eval_merge]

theorem integerMergeCheck3 : integerMerge3 =
    Integer.Sparse.merge integerTerm3 integerMerge2 := by decide +kernel

theorem integerMergeEval3 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge3 x =
      Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck3, Integer.Sparse.eval_merge]
  rw [integerMergeEval2]
  all_goals ring

theorem integerMergeCheck4 : integerMerge4 =
    Integer.Sparse.merge integerMerge1 integerMerge3 := by decide +kernel

theorem integerMergeEval4 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge4 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck4, Integer.Sparse.eval_merge]
  rw [integerMergeEval1, integerMergeEval3]
  all_goals ring

theorem integerMergeCheck5 : integerMerge5 =
    Integer.Sparse.merge integerTerm7 integerTerm8 := by decide +kernel

theorem integerMergeEval5 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge5 x =
      Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck5, Integer.Sparse.eval_merge]

theorem integerMergeCheck6 : integerMerge6 =
    Integer.Sparse.merge integerTerm6 integerMerge5 := by decide +kernel

theorem integerMergeEval6 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge6 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck6, Integer.Sparse.eval_merge]
  rw [integerMergeEval5]
  all_goals ring

theorem integerMergeCheck7 : integerMerge7 =
    Integer.Sparse.merge integerTerm9 integerTerm10 := by decide +kernel

theorem integerMergeEval7 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge7 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x := by
  rw [integerMergeCheck7, Integer.Sparse.eval_merge]

theorem integerMergeCheck8 : integerMerge8 =
    Integer.Sparse.merge integerTerm11 integerTerm12 := by decide +kernel

theorem integerMergeEval8 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge8 x =
      Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck8, Integer.Sparse.eval_merge]

theorem integerMergeCheck9 : integerMerge9 =
    Integer.Sparse.merge integerMerge7 integerMerge8 := by decide +kernel

theorem integerMergeEval9 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge9 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck9, Integer.Sparse.eval_merge]
  rw [integerMergeEval7, integerMergeEval8]
  all_goals ring

theorem integerMergeCheck10 : integerMerge10 =
    Integer.Sparse.merge integerMerge6 integerMerge9 := by decide +kernel

theorem integerMergeEval10 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge10 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck10, Integer.Sparse.eval_merge]
  rw [integerMergeEval6, integerMergeEval9]
  all_goals ring

theorem integerMergeCheck11 : integerMerge11 =
    Integer.Sparse.merge integerMerge4 integerMerge10 := by decide +kernel

theorem integerMergeEval11 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge11 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck11, Integer.Sparse.eval_merge]
  rw [integerMergeEval4, integerMergeEval10]
  all_goals ring

theorem integerMergeCheck12 : integerMerge12 =
    Integer.Sparse.merge integerTerm14 integerTerm15 := by decide +kernel

theorem integerMergeEval12 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge12 x =
      Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck12, Integer.Sparse.eval_merge]

theorem integerMergeCheck13 : integerMerge13 =
    Integer.Sparse.merge integerTerm13 integerMerge12 := by decide +kernel

theorem integerMergeEval13 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge13 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck13, Integer.Sparse.eval_merge]
  rw [integerMergeEval12]
  all_goals ring

theorem integerMergeCheck14 : integerMerge14 =
    Integer.Sparse.merge integerTerm17 integerTerm18 := by decide +kernel

theorem integerMergeEval14 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge14 x =
      Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck14, Integer.Sparse.eval_merge]

theorem integerMergeCheck15 : integerMerge15 =
    Integer.Sparse.merge integerTerm16 integerMerge14 := by decide +kernel

theorem integerMergeEval15 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge15 x =
      Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck15, Integer.Sparse.eval_merge]
  rw [integerMergeEval14]
  all_goals ring

theorem integerMergeCheck16 : integerMerge16 =
    Integer.Sparse.merge integerMerge13 integerMerge15 := by decide +kernel

theorem integerMergeEval16 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge16 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck16, Integer.Sparse.eval_merge]
  rw [integerMergeEval13, integerMergeEval15]
  all_goals ring

theorem integerMergeCheck17 : integerMerge17 =
    Integer.Sparse.merge integerTerm20 integerTerm21 := by decide +kernel

theorem integerMergeEval17 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge17 x =
      Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck17, Integer.Sparse.eval_merge]

theorem integerMergeCheck18 : integerMerge18 =
    Integer.Sparse.merge integerTerm19 integerMerge17 := by decide +kernel

theorem integerMergeEval18 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge18 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck18, Integer.Sparse.eval_merge]
  rw [integerMergeEval17]
  all_goals ring

theorem integerMergeCheck19 : integerMerge19 =
    Integer.Sparse.merge integerTerm22 integerTerm23 := by decide +kernel

theorem integerMergeEval19 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge19 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x := by
  rw [integerMergeCheck19, Integer.Sparse.eval_merge]

theorem integerMergeCheck20 : integerMerge20 =
    Integer.Sparse.merge integerTerm24 integerTerm25 := by decide +kernel

theorem integerMergeEval20 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge20 x =
      Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck20, Integer.Sparse.eval_merge]

theorem integerMergeCheck21 : integerMerge21 =
    Integer.Sparse.merge integerMerge19 integerMerge20 := by decide +kernel

theorem integerMergeEval21 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge21 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck21, Integer.Sparse.eval_merge]
  rw [integerMergeEval19, integerMergeEval20]
  all_goals ring

theorem integerMergeCheck22 : integerMerge22 =
    Integer.Sparse.merge integerMerge18 integerMerge21 := by decide +kernel

theorem integerMergeEval22 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge22 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck22, Integer.Sparse.eval_merge]
  rw [integerMergeEval18, integerMergeEval21]
  all_goals ring

theorem integerMergeCheck23 : integerMerge23 =
    Integer.Sparse.merge integerMerge16 integerMerge22 := by decide +kernel

theorem integerMergeEval23 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge23 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck23, Integer.Sparse.eval_merge]
  rw [integerMergeEval16, integerMergeEval22]
  all_goals ring

theorem integerMergeCheck24 : integerMerge24 =
    Integer.Sparse.merge integerMerge11 integerMerge23 := by decide +kernel

theorem integerMergeEval24 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge24 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x + Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck24, Integer.Sparse.eval_merge]
  rw [integerMergeEval11, integerMergeEval23]
  all_goals ring

theorem finalReindex0 : List.Perm
    (Integer.Sparse.reindex PairSourceBridge.coordinateMap PairData.target0) integerMerge24 := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

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

theorem sum_fin_two {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_PartitionRules
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem partitionWeight2_0 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 0) ↪ Coord) : ℝ) / 6 ^ 2 = (1/6 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 2 = (1/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight2_1 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 1) ↪ Coord) : ℝ) / 6 ^ 2 = (5/6 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 2 = (5/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition2 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 2) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family2 EqualityPatterns.covers2
  rw [MixedSemantics.sum_fin_two] at h
  simpa only [partitionWeight2_0, partitionWeight2_1] using h

theorem partitionWeight3_0 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 0) ↪ Coord) : ℝ) / 6 ^ 3 = (1/36 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 3 = (1/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_1 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 1) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_2 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 2) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_3 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 3) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_4 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 4) ↪ Coord) : ℝ) / 6 ^ 3 = (5/9 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/9 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition3 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 3) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family3 EqualityPatterns.covers3
  rw [MixedSemantics.sum_fin_five] at h
  simpa only [partitionWeight3_0, partitionWeight3_1, partitionWeight3_2, partitionWeight3_3, partitionWeight3_4] using h

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition0 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term0.charges u j)).re) =
      Sparse.eval monomialValue0 (momentVector H) := by
  let A : Matrix Coord (Fin 2) ℤ := term0.charges
  change pairAverage H (fun K => (∏ j : Fin 2, g K (fun u => A u j)).re) = _
  have hp := pair_partition2 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  rw [hm0, hm1] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2, EqualityPatterns.blocks2, Nat.descFactorial, monomialValue0, value0, value117, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm0 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term0 =
      Integer.Sparse.eval integerTerm0 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition0 hH]
  norm_num [term0, integerTerm0, monomialValue0, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical0 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw0 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw0 = injectiveMoment H extraRaw0step0 := by
      have heq : extraRaw0step0 = -extraRaw0 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw0).symm
    injectiveMoment H extraRaw0step0 = injectiveMoment H extraRaw0step1 := by
      have hz : ∀ j, extraRaw0step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw0step1 = (fun u v => extraRaw0step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw0step0 extraPermutation62 hz
    injectiveMoment H extraRaw0step1 = injectiveMoment H extraRaw0step2 := by
      have heq : extraRaw0step2 = (fun u v => extraRaw0step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw0step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node856 := by rfl

theorem extraCanonical1 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw1 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw1 = injectiveMoment H extraRaw1step0 := by
      have heq : extraRaw1step0 = -extraRaw1 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw1).symm
    injectiveMoment H extraRaw1step0 = injectiveMoment H extraRaw1step1 := by
      have hz : ∀ j, extraRaw1step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw1step1 = (fun u v => extraRaw1step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw1step0 extraPermutation62 hz
    injectiveMoment H extraRaw1step1 = injectiveMoment H extraRaw1step2 := by
      have heq : extraRaw1step2 = (fun u v => extraRaw1step1 (extraPermutation24 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw1step1 extraPermutation24 extraPermutation5
    _ = injectiveMoment H node545 := by rfl

theorem extraCanonical2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw2 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw2 = injectiveMoment H extraRaw2step0 := by
      have hz : ∀ j, extraRaw2 (extraPermutation66 0) j = 0 := by decide +kernel
      have heq : extraRaw2step0 = (fun u v => extraRaw2 (extraPermutation66 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2 extraPermutation66 hz
    injectiveMoment H extraRaw2step0 = injectiveMoment H extraRaw2step1 := by
      have hz : ∀ j, extraRaw2step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw2step1 = (fun u v => extraRaw2step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw2step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

theorem extraCanonical3 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw3 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw3 = injectiveMoment H extraRaw3step0 := by
      have heq : extraRaw3step0 = -extraRaw3 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw3).symm
    injectiveMoment H extraRaw3step0 = injectiveMoment H extraRaw3step1 := by
      have hz : ∀ j, extraRaw3step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw3step1 = (fun u v => extraRaw3step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw3step0 extraPermutation62 hz
    injectiveMoment H extraRaw3step1 = injectiveMoment H extraRaw3step2 := by
      have heq : extraRaw3step2 = (fun u v => extraRaw3step1 (extraPermutation26 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw3step1 extraPermutation26 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

theorem extraCanonical4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw4 = injectiveMoment H node65 := by
  calc
    injectiveMoment H extraRaw4 = injectiveMoment H extraRaw4step0 := by
      have hz : ∀ j, extraRaw4 (extraPermutation67 0) j = 0 := by decide +kernel
      have heq : extraRaw4step0 = (fun u v => extraRaw4 (extraPermutation67 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4 extraPermutation67 hz
    injectiveMoment H extraRaw4step0 = injectiveMoment H extraRaw4step1 := by
      have hz : ∀ j, extraRaw4step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw4step1 = (fun u v => extraRaw4step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw4step0 extraPermutation39 hz
    _ = injectiveMoment H node65 := by rfl

theorem extraCanonical5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H extraRaw5 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw5 = injectiveMoment H extraRaw5step0 := by
      have heq : extraRaw5step0 = -extraRaw5 := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH extraRaw5).symm
    injectiveMoment H extraRaw5step0 = injectiveMoment H extraRaw5step1 := by
      have hz : ∀ j, extraRaw5step0 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw5step1 = (fun u v => extraRaw5step0 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw5step0 extraPermutation62 hz
    injectiveMoment H extraRaw5step1 = injectiveMoment H extraRaw5step2 := by
      have heq : extraRaw5step2 = (fun u v => extraRaw5step1 (extraPermutation28 u) (extraPermutation5 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw5step1 extraPermutation28 extraPermutation5
    _ = injectiveMoment H node858 := by rfl

theorem extraCanonical6 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw6 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw6 = injectiveMoment H extraRaw6step0 := by
      have hz : ∀ j, extraRaw6 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw6step0 = (fun u v => extraRaw6 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw6 extraPermutation62 hz
    injectiveMoment H extraRaw6step0 = injectiveMoment H extraRaw6step1 := by
      have heq : extraRaw6step1 = (fun u v => extraRaw6step0 (extraPermutation24 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw6step0 extraPermutation24 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

theorem extraCanonical7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw7 = injectiveMoment H node856 := by
  calc
    injectiveMoment H extraRaw7 = injectiveMoment H extraRaw7step0 := by
      have hz : ∀ j, extraRaw7 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw7step0 = (fun u v => extraRaw7 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw7 extraPermutation62 hz
    _ = injectiveMoment H node856 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition1 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term1.charges u j)).re) =
      Sparse.eval monomialValue1 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term1.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5127 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw0 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical0 hH).trans (sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue1, value0, value117, value232, value65, value856, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm1 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term1 =
      Integer.Sparse.eval integerTerm1 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition1 hH]
  norm_num [term1, integerTerm1, monomialValue1, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw35 = injectiveMoment H node232 := by
  calc
    injectiveMoment H extraRaw35 = injectiveMoment H extraRaw35step0 := by
      have hz : ∀ j, extraRaw35 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw35step0 = (fun u v => extraRaw35 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw35 extraPermutation62 hz
    injectiveMoment H extraRaw35step0 = injectiveMoment H extraRaw35step1 := by
      have heq : extraRaw35step1 = (fun u v => extraRaw35step0 (extraPermutation34 u) (extraPermutation1 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw35step0 extraPermutation34 extraPermutation1
    _ = injectiveMoment H node232 := by rfl

theorem extraCanonical36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw36 = injectiveMoment H node545 := by
  calc
    injectiveMoment H extraRaw36 = injectiveMoment H extraRaw36step0 := by
      have hz : ∀ j, extraRaw36 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw36step0 = (fun u v => extraRaw36 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw36 extraPermutation62 hz
    _ = injectiveMoment H node545 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition10 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term10.charges u j)).re) =
      Sparse.eval monomialValue10 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term10.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw35 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical35 hH).trans (sound232 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw5164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5164 hH).trans (sound11 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value545 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw36 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical36 hH).trans (sound545 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue10, value0, value11, value117, value232, value545, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm10 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term10 =
      Integer.Sparse.eval integerTerm10 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition10 hH]
  norm_num [term10, integerTerm10, monomialValue10, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical63 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw63 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw63 = injectiveMoment H extraRaw63step0 := by
      have hz : ∀ j, extraRaw63 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw63step0 = (fun u v => extraRaw63 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63 extraPermutation63 hz
    injectiveMoment H extraRaw63step0 = injectiveMoment H extraRaw63step1 := by
      have hz : ∀ j, extraRaw63step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw63step1 = (fun u v => extraRaw63step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw63step0 extraPermutation39 hz
    injectiveMoment H extraRaw63step1 = injectiveMoment H extraRaw63step2 := by
      have heq : extraRaw63step2 = (fun u v => extraRaw63step1 (extraPermutation19 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw63step1 extraPermutation19 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical64 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw64 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw64 = injectiveMoment H extraRaw64step0 := by
      have hz : ∀ j, extraRaw64 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw64step0 = (fun u v => extraRaw64 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw64 extraPermutation62 hz
    injectiveMoment H extraRaw64step0 = injectiveMoment H extraRaw64step1 := by
      have heq : extraRaw64step1 = (fun u v => extraRaw64step0 (extraPermutation26 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw64step0 extraPermutation26 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition15 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term15.charges u j)).re) =
      Sparse.eval monomialValue15 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term15.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw63 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical63 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = extraRaw2 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical2 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw64 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical64 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue15, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm15 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term15 =
      Integer.Sparse.eval integerTerm15 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition15 hH]
  norm_num [term15, integerTerm15, monomialValue15, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_ExtraCanonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical90 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw90 = injectiveMoment H node46 := by
  calc
    injectiveMoment H extraRaw90 = injectiveMoment H extraRaw90step0 := by
      have hz : ∀ j, extraRaw90 (extraPermutation63 0) j = 0 := by decide +kernel
      have heq : extraRaw90step0 = (fun u v => extraRaw90 (extraPermutation63 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90 extraPermutation63 hz
    injectiveMoment H extraRaw90step0 = injectiveMoment H extraRaw90step1 := by
      have hz : ∀ j, extraRaw90step0 (extraPermutation39 0) j = 0 := by decide +kernel
      have heq : extraRaw90step1 = (fun u v => extraRaw90step0 (extraPermutation39 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw90step0 extraPermutation39 hz
    injectiveMoment H extraRaw90step1 = injectiveMoment H extraRaw90step2 := by
      have heq : extraRaw90step2 = (fun u v => extraRaw90step1 (extraPermutation23 u) (extraPermutation0 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw90step1 extraPermutation23 extraPermutation0
    _ = injectiveMoment H node46 := by rfl

theorem extraCanonical91 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw91 = injectiveMoment H node858 := by
  calc
    injectiveMoment H extraRaw91 = injectiveMoment H extraRaw91step0 := by
      have hz : ∀ j, extraRaw91 (extraPermutation62 0) j = 0 := by decide +kernel
      have heq : extraRaw91step0 = (fun u v => extraRaw91 (extraPermutation62 u.succ) v) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H extraRaw91 extraPermutation62 hz
    injectiveMoment H extraRaw91step0 = injectiveMoment H extraRaw91step1 := by
      have heq : extraRaw91step1 = (fun u v => extraRaw91step0 (extraPermutation28 u) (extraPermutation2 v)) := by
        ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
      rw [heq]
      exact moment_permute H extraRaw91step0 extraPermutation28 extraPermutation2
    _ = injectiveMoment H node858 := by rfl

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition2 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term2.charges u j)).re) =
      Sparse.eval monomialValue2 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term2.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw7625 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7625 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = raw5164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5164 hH).trans (sound11 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value545 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw1 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical1 hH).trans (sound545 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue2, value0, value11, value117, value232, value545, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm2 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term2 =
      Integer.Sparse.eval integerTerm2 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition2 hH]
  norm_num [term2, integerTerm2, monomialValue2, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition20 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term20.charges u j)).re) =
      Sparse.eval monomialValue20 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term20.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw90 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical90 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = extraRaw4 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical4 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw91 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical91 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue20, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm20 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term20 =
      Integer.Sparse.eval integerTerm20 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition20 hH]
  norm_num [term20, integerTerm20, monomialValue20, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition3 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term3.charges u j)).re) =
      Sparse.eval monomialValue3 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term3.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5124 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5124 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw2 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical2 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw3 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical3 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue3, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm3 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term3 =
      Integer.Sparse.eval integerTerm3 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition3 hH]
  norm_num [term3, integerTerm3, monomialValue3, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition4 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term4.charges u j)).re) =
      Sparse.eval monomialValue4 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term4.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5123 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5123 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw4 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical4 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw5 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical5 hH).trans (sound858 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue4, value0, value117, value46, value65, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm4 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term4 =
      Integer.Sparse.eval integerTerm4 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition4 hH]
  norm_num [term4, integerTerm4, monomialValue4, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

theorem partition5 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term5.charges u j)).re) =
      Sparse.eval monomialValue5 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term5.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = extraRaw6 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical6 hH).trans (sound232 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw7 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical7 hH).trans (sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue5, value0, value117, value232, value65, value856, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Weighted5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm5 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term5 =
      Integer.Sparse.eval integerTerm5 (PairSemantics.momentVector H) := by
  unfold weightedAverage
  rw [partition5 hH]
  norm_num [term5, integerTerm5, monomialValue5, Sparse.eval, Integer.Sparse.eval]
  all_goals ring

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem expandedIdentity0 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * expanded0 H =
      Integer.Sparse.eval integerMerge24 (PairSemantics.momentVector H) := by
  rw [integerMergeEval24]
  unfold expanded0
  rw [sum_terms0_expand]
  simp only [mul_add]
  rw [weightedTerm0 hH, weightedTerm1 hH, weightedTerm2 hH, weightedTerm3 hH, weightedTerm4 hH, weightedTerm5 hH, weightedTerm6_e hH, weightedTerm7_e hH, weightedTerm8_e hH, weightedTerm9_e hH, weightedTerm10 hH, weightedTerm11_e hH, weightedTerm12_e hH, weightedTerm13_e hH, weightedTerm14_e hH, weightedTerm15 hH, weightedTerm16_e hH, weightedTerm17_e hH, weightedTerm18_e hH, weightedTerm19_e hH, weightedTerm20 hH, weightedTerm21_e hH, weightedTerm22_e hH, weightedTerm23_e hH, weightedTerm24_e hH, weightedTerm25_e hH]

theorem certificate_zero0 {H : CMatrix} (hH : IsHadamard H) : expanded0 H = 0 := by
  have hz := PairSourceBridge.targetZero0_e hH
  unfold PairSourceBridge.momentVector at hz
  rw [← Integer.Sparse.eval_reindex] at hz
  rw [Integer.Sparse.eval_perm finalReindex0] at hz
  have he := expandedIdentity0 hH
  rw [hz] at he
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_FourierTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem pair_cross_certificate_e_oai {H : CMatrix} (hH : IsHadamard H) :
    PairCertificateIdentity H qCross := by
  unfold PairCertificateIdentity
  rw [← Certificate.PairTargetSemantics.expanded_identity0 hH]
  exact Certificate.PairTargetSemantics.certificate_zero0 hH

end MUB6

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.pair_cross_certificate_e_oai := @OAI.MUB6.pair_cross_certificate_e_oai
