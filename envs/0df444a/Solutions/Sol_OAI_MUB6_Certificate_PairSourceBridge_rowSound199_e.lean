-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T14:03:45.779628+00:00
-- url     : https://prove2.me/submissions/89ca8e34-2980-4910-bad0-d0d81fd188b6

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E149
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3300_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3351_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3467_e

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

/-- At saturation the old labels exhaust the population, so only the occupied
contractions occur. This statement never defines a seven-row moment. -/
theorem saturated_average_contraction (n : ℕ)
    (f : (Fin n ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin n, average (fun e : Fin n ↪ Fin n => f e (e j))) = 0 := by
  simp only [average]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs : (∑ e : Fin n ↪ Fin n, ∑ j : Fin n, f e (e j)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have he : Function.Bijective e :=
      ⟨e.injective, Finite.surjective_of_injective e.injective⟩
    rw [he.sum_comp]
    exact h e
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

/-- The seven-row boundary equation. All six terms are moments of six-row
matrices. There is no term for sampling seven distinct labels from six. -/
theorem injectiveMoment_seven_row_boundary {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin 7) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    (∑ j : Fin 6, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.saturated_average_contraction 6
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord => ∑ j : Fin 6,
      average (fun ρ : Fin 6 ↪ Coord => contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_occupied hH,
    contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8316 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8316 = injectiveMoment H raw8316step0 := by
      have heq : raw8316step0 = -raw8316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8316).symm
    injectiveMoment H raw8316step0 = injectiveMoment H raw8316step1 := by
      have hz : ∀ i, raw8316step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8316step1 = (fun i j => raw8316step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8316step0 permutation9 hz
    injectiveMoment H raw8316step1 = injectiveMoment H raw8316step2 := by
      have heq : raw8316step2 = (fun i j => raw8316step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8316step1 permutation8 permutation3
    _ = injectiveMoment H node44 := by rfl

theorem canonical8319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8319 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw8319 = injectiveMoment H raw8319step0 := by
      have heq : raw8319step0 = (fun i j => raw8319 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8319 permutation258 permutation9
    _ = injectiveMoment H node3300 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical287
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9206 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw9206 = injectiveMoment H raw9206step0 := by
      have heq : raw9206step0 = (fun i j => raw9206 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9206 permutation277 permutation9
    _ = injectiveMoment H node3300 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9253 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw9253 = injectiveMoment H raw9253step0 := by
      have heq : raw9253step0 = (fun i j => raw9253 (permutation283 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9253 permutation283 permutation9
    _ = injectiveMoment H node3300 := by rfl

theorem canonical9269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9269 = injectiveMoment H node3287 := by
  calc
    injectiveMoment H raw9269 = injectiveMoment H raw9269step0 := by
      have heq : raw9269step0 = (fun i j => raw9269 (permutation241 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9269 permutation241 permutation15
    _ = injectiveMoment H node3287 := by rfl

theorem canonical9272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9272 = injectiveMoment H node3351 := by
  calc
    injectiveMoment H raw9272 = injectiveMoment H raw9272step0 := by
      have heq : raw9272step0 = -raw9272 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9272).symm
    injectiveMoment H raw9272step0 = injectiveMoment H raw9272step1 := by
      have heq : raw9272step1 = (fun i j => raw9272step0 (permutation309 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9272step0 permutation309 permutation15
    _ = injectiveMoment H node3351 := by rfl

theorem canonical9275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9275 = injectiveMoment H node3467 := by
  calc
    injectiveMoment H raw9275 = injectiveMoment H raw9275step0 := by
      have heq : raw9275step0 = (fun i j => raw9275 (permutation242 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9275 permutation242 permutation15
    _ = injectiveMoment H node3467 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2524 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw2524 = injectiveMoment H raw2524step0 := by
      have heq : raw2524step0 = raw2524.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2524).symm
    injectiveMoment H raw2524step0 = injectiveMoment H raw2524step1 := by
      have heq : raw2524step1 = (fun i j => raw2524step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2524step0 permutation10 permutation3
    _ = injectiveMoment H node134 := by rfl

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

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

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

theorem canonical6889 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6889 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw6889 = injectiveMoment H raw6889step0 := by
      have heq : raw6889step0 = raw6889.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6889).symm
    injectiveMoment H raw6889step0 = injectiveMoment H raw6889step1 := by
      have heq : raw6889step1 = -raw6889step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6889step0).symm
    injectiveMoment H raw6889step1 = injectiveMoment H raw6889step2 := by
      have heq : raw6889step2 = (fun i j => raw6889step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6889step1 permutation26 permutation3
    _ = injectiveMoment H node225 := by rfl

theorem canonical6895 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6895 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6895 = injectiveMoment H raw6895step0 := by
      have heq : raw6895step0 = raw6895.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6895).symm
    injectiveMoment H raw6895step0 = injectiveMoment H raw6895step1 := by
      have heq : raw6895step1 = -raw6895step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6895step0).symm
    injectiveMoment H raw6895step1 = injectiveMoment H raw6895step2 := by
      have heq : raw6895step2 = (fun i j => raw6895step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6895step1 permutation26 permutation3
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

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

theorem sound134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node134 = Sparse.eval value134 (momentVector H) := by
  have hc : momentVector H 81 = injectiveMoment H node134 := rfl
  simp [value134, Sparse.eval, hc]

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

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node219 = Sparse.eval value219 (momentVector H) := by
  have hc : momentVector H 796 = injectiveMoment H node219 := rfl
  simp [value219, Sparse.eval, hc]

theorem sound223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node223 = Sparse.eval value223 (momentVector H) := by
  have hc : momentVector H 56 = injectiveMoment H node223 := rfl
  simp [value223, Sparse.eval, hc]

theorem sound225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node225 = Sparse.eval value225 (momentVector H) := by
  have hc : momentVector H 228 = injectiveMoment H node225 := rfl
  simp [value225, Sparse.eval, hc]

theorem sound229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node229 = Sparse.eval value229 (momentVector H) := by
  have heq : pivotMatrix229 = (fun u v => node229 (pivotPermutation229 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node229 = injectiveMoment H pivotMatrix229 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix229 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix229 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix229 (2 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node229 + (injectiveMoment H (mergeFirst pivotMatrix229 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix229 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value229, value36, value43, value44, Sparse.eval] at hc ⊢
  linarith

theorem sound230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node230 = Sparse.eval value230 (momentVector H) := by
  have heq : pivotMatrix230 = (fun u v => node230 (pivotPermutation230 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node230 = injectiveMoment H pivotMatrix230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix230 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix230 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (1 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (2 : Fin 3) = raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4967 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node230 + (injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value230, value44, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3661 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3661 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw3661 = injectiveMoment H raw3661step0 := by
      have heq : raw3661step0 = raw3661.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3661).symm
    injectiveMoment H raw3661step0 = injectiveMoment H raw3661step1 := by
      have heq : raw3661step1 = -raw3661step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3661step0).symm
    injectiveMoment H raw3661step1 = injectiveMoment H raw3661step2 := by
      have heq : raw3661step2 = (fun i j => raw3661step1 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3661step1 permutation31 permutation15
    _ = injectiveMoment H node473 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6335 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6335 = injectiveMoment H raw6335step0 := by
      have heq : raw6335step0 = raw6335.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6335).symm
    injectiveMoment H raw6335step0 = injectiveMoment H raw6335step1 := by
      have heq : raw6335step1 = -raw6335step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6335step0).symm
    injectiveMoment H raw6335step1 = injectiveMoment H raw6335step2 := by
      have heq : raw6335step2 = (fun i j => raw6335step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6335step1 permutation15 permutation8
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6562 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6562 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6562 = injectiveMoment H raw6562step0 := by
      have heq : raw6562step0 = raw6562.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6562).symm
    injectiveMoment H raw6562step0 = injectiveMoment H raw6562step1 := by
      have heq : raw6562step1 = -raw6562step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6562step0).symm
    injectiveMoment H raw6562step1 = injectiveMoment H raw6562step2 := by
      have heq : raw6562step2 = (fun i j => raw6562step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6562step1 permutation31 permutation3
    _ = injectiveMoment H node230 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6223 = injectiveMoment H node945 := by
  rfl

theorem canonical6225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6225 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6225 = injectiveMoment H raw6225step0 := by
      have heq : raw6225step0 = raw6225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6225).symm
    injectiveMoment H raw6225step0 = injectiveMoment H raw6225step1 := by
      have heq : raw6225step1 = -raw6225step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6225step0).symm
    injectiveMoment H raw6225step1 = injectiveMoment H raw6225step2 := by
      have heq : raw6225step2 = (fun i j => raw6225step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6225step1 permutation21 permutation6
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node896 = Sparse.eval value896 (momentVector H) := by
  have heq : pivotMatrix896 = (fun u v => node896.transpose (pivotPermutation896 u) v) := by apply Matrix.ext; unfold pivotMatrix896 node896 pivotPermutation896; decide +kernel
  have hmoment : injectiveMoment H node896 = injectiveMoment H pivotMatrix896 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix896 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix896 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (0 : Fin 3) = raw2524 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw2524; decide +kernel
    rw [heq]
    exact (canonical2524 hH).trans (sound134 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (1 : Fin 3) = raw6889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6889; decide +kernel
    rw [heq]
    exact (canonical6889 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix896 (2 : Fin 3) = raw6895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix896 raw6895; decide +kernel
    rw [heq]
    exact (canonical6895 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node896 + (injectiveMoment H (mergeFirst pivotMatrix896 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix896 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value896, value134, value225, value229, Sparse.eval] at hc ⊢
  linarith

theorem sound945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node945 = Sparse.eval value945 (momentVector H) := by
  have heq : pivotMatrix945 = (fun u v => node945 (pivotPermutation945 u) v) := by apply Matrix.ext; unfold pivotMatrix945 node945 pivotPermutation945; decide +kernel
  have hmoment : injectiveMoment H node945 = injectiveMoment H pivotMatrix945 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix945 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix945 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (1 : Fin 3) = raw6335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6335; decide +kernel
    rw [heq]
    exact (canonical6335 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node945 + (injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value945, value229, value44, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6418 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6418 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw6418 = injectiveMoment H raw6418step0 := by
      have heq : raw6418step0 = raw6418.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6418).symm
    injectiveMoment H raw6418step0 = injectiveMoment H raw6418step1 := by
      have heq : raw6418step1 = -raw6418step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6418step0).symm
    injectiveMoment H raw6418step1 = injectiveMoment H raw6418step2 := by
      have heq : raw6418step2 = (fun i j => raw6418step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6418step1 permutation22 permutation5
    _ = injectiveMoment H node210 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2188 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw2188 = injectiveMoment H raw2188step0 := by
      have heq : raw2188step0 = raw2188.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2188).symm
    injectiveMoment H raw2188step0 = injectiveMoment H raw2188step1 := by
      have heq : raw2188step1 = -raw2188step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2188step0).symm
    injectiveMoment H raw2188step1 = injectiveMoment H raw2188step2 := by
      have heq : raw2188step2 = (fun i j => raw2188step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2188step1 permutation28 permutation17
    _ = injectiveMoment H node1208 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1009 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1009 = Sparse.eval value1009 (momentVector H) := by
  have heq : pivotMatrix1009 = (fun u v => node1009 (pivotPermutation1009 u) v) := by apply Matrix.ext; unfold pivotMatrix1009 node1009 pivotPermutation1009; decide +kernel
  have hmoment : injectiveMoment H node1009 = injectiveMoment H pivotMatrix1009 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1009 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1009 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (1 : Fin 3) = raw6562 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6562; decide +kernel
    rw [heq]
    exact (canonical6562 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1009 (2 : Fin 3) = raw6418 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1009 raw6418; decide +kernel
    rw [heq]
    exact (canonical6418 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1009 + (injectiveMoment H (mergeFirst pivotMatrix1009 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1009 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1009, value210, value230, value44, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8884 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8884 = injectiveMoment H node219 := by
  calc
    injectiveMoment H raw8884 = injectiveMoment H raw8884step0 := by
      have heq : raw8884step0 = raw8884.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8884).symm
    injectiveMoment H raw8884step0 = injectiveMoment H raw8884step1 := by
      have heq : raw8884step1 = -raw8884step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8884step0).symm
    injectiveMoment H raw8884step1 = injectiveMoment H raw8884step2 := by
      have heq : raw8884step2 = (fun i j => raw8884step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8884step1 permutation21 permutation4
    _ = injectiveMoment H node219 := by rfl

theorem canonical8887 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8887 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw8887 = injectiveMoment H raw8887step0 := by
      have heq : raw8887step0 = raw8887.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8887).symm
    injectiveMoment H raw8887step0 = injectiveMoment H raw8887step1 := by
      have heq : raw8887step1 = -raw8887step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8887step0).symm
    injectiveMoment H raw8887step1 = injectiveMoment H raw8887step2 := by
      have heq : raw8887step2 = (fun i j => raw8887step1 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8887step1 permutation21 permutation4
    _ = injectiveMoment H node223 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical278
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8896 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw8896 = injectiveMoment H raw8896step0 := by
      have heq : raw8896step0 = raw8896.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8896).symm
    injectiveMoment H raw8896step0 = injectiveMoment H raw8896step1 := by
      have heq : raw8896step1 = -raw8896step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8896step0).symm
    injectiveMoment H raw8896step1 = injectiveMoment H raw8896step2 := by
      have heq : raw8896step2 = (fun i j => raw8896step1 (permutation14 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8896step1 permutation14 permutation7
    _ = injectiveMoment H node210 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1172 = Sparse.eval value1172 (momentVector H) := by
  have heq : pivotMatrix1172 = (fun u v => node1172.transpose (pivotPermutation1172 u) v) := by apply Matrix.ext; unfold pivotMatrix1172 node1172 pivotPermutation1172; decide +kernel
  have hmoment : injectiveMoment H node1172 = injectiveMoment H pivotMatrix1172 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1172 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1172 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1172 (0 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (0 : Fin 3) = raw6889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw6889; decide +kernel
    rw [heq]
    exact (canonical6889 hH).trans (sound225 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1172 (1 : Fin 3)) =
      Sparse.eval value219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (1 : Fin 3) = raw8884 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw8884; decide +kernel
    rw [heq]
    exact (canonical8884 hH).trans (sound219 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1172 (2 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1172 (2 : Fin 3) = raw8887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1172 raw8887; decide +kernel
    rw [heq]
    exact (canonical8887 hH).trans (sound223 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1172 + (injectiveMoment H (mergeFirst pivotMatrix1172 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1172 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1172 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1172, value219, value223, value225, Sparse.eval] at hc ⊢
  linarith

theorem sound1208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1208 = Sparse.eval value1208 (momentVector H) := by
  have heq : pivotMatrix1208 = (fun u v => node1208.transpose (pivotPermutation1208 u) v) := by apply Matrix.ext; unfold pivotMatrix1208 node1208 pivotPermutation1208; decide +kernel
  have hmoment : injectiveMoment H node1208 = injectiveMoment H pivotMatrix1208 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1208 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1208 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1208 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (0 : Fin 3) = raw6895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw6895; decide +kernel
    rw [heq]
    exact (canonical6895 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1208 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (1 : Fin 3) = raw8887 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw8887; decide +kernel
    rw [heq]
    exact (canonical8887 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1208 (2 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1208 (2 : Fin 3) = raw8896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1208 raw8896; decide +kernel
    rw [heq]
    exact (canonical8896 hH).trans (sound210 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1208 + (injectiveMoment H (mergeFirst pivotMatrix1208 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1208 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1208 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1208, value210, value223, value229, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node449 = Sparse.eval value449 (momentVector H) := by
  have hc : momentVector H 83 = injectiveMoment H node449 := rfl
  simp [value449, Sparse.eval, hc]

theorem sound473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node473 = Sparse.eval value473 (momentVector H) := by
  have hc : momentVector H 37 = injectiveMoment H node473 := rfl
  simp [value473, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1499 = injectiveMoment H node449 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1511 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1511 = injectiveMoment H raw1511step0 := by
      have heq : raw1511step0 = raw1511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1511).symm
    injectiveMoment H raw1511step0 = injectiveMoment H raw1511step1 := by
      have heq : raw1511step1 = (fun i j => raw1511step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1511step0 permutation30 permutation30
    _ = injectiveMoment H node896 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1735 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw1735 = injectiveMoment H raw1735step0 := by
      have heq : raw1735step0 = raw1735.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1735).symm
    injectiveMoment H raw1735step0 = injectiveMoment H raw1735step1 := by
      have heq : raw1735step1 = (fun i j => raw1735step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1735step0 permutation32 permutation32
    _ = injectiveMoment H node896 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node692 = Sparse.eval value692 (momentVector H) := by
  have hc : momentVector H 784 = injectiveMoment H node692 := rfl
  simp [value692, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node579 = Sparse.eval value579 (momentVector H) := by
  have hc : momentVector H 501 = injectiveMoment H node579 := rfl
  simp [value579, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound24
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1580 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1580 = Sparse.eval value1580 (momentVector H) := by
  have heq : pivotMatrix1580 = (fun u v => node1580 (pivotPermutation1580 u) v) := by apply Matrix.ext; unfold pivotMatrix1580 node1580 pivotPermutation1580; decide +kernel
  have hmoment : injectiveMoment H node1580 = injectiveMoment H pivotMatrix1580 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1580 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1580 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1580 (0 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (0 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1580 (1 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (1 : Fin 4) = raw1735 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1735; decide +kernel
    rw [heq]
    exact (canonical1735 hH).trans (sound896 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1580 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (2 : Fin 4) = raw1511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1511; decide +kernel
    rw [heq]
    exact (canonical1511 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1580 (3 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1580 (3 : Fin 4) = raw1499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1580 raw1499; decide +kernel
    rw [heq]
    exact (canonical1499 hH).trans (sound449 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1580 + (injectiveMoment H (mergeFirst pivotMatrix1580 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1580 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1580, value449, value896, value945, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3707 = injectiveMoment H node945 := by
  calc
    injectiveMoment H raw3707 = injectiveMoment H raw3707step0 := by
      have heq : raw3707step0 = -raw3707 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3707).symm
    injectiveMoment H raw3707step0 = injectiveMoment H raw3707step1 := by
      have heq : raw3707step1 = (fun i j => raw3707step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3707step0 permutation31 permutation15
    _ = injectiveMoment H node945 := by rfl

theorem canonical3710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3710 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3710 = injectiveMoment H raw3710step0 := by
      have heq : raw3710step0 = -raw3710 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3710).symm
    injectiveMoment H raw3710step0 = injectiveMoment H raw3710step1 := by
      have heq : raw3710step1 = (fun i j => raw3710step0 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3710step0 permutation25 permutation16
    _ = injectiveMoment H node1009 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4344 = injectiveMoment H node1172 := by
  calc
    injectiveMoment H raw4344 = injectiveMoment H raw4344step0 := by
      have heq : raw4344step0 = raw4344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4344).symm
    injectiveMoment H raw4344step0 = injectiveMoment H raw4344step1 := by
      have heq : raw4344step1 = -raw4344step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4344step0).symm
    injectiveMoment H raw4344step1 = injectiveMoment H raw4344step2 := by
      have heq : raw4344step2 = (fun i j => raw4344step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4344step1 permutation27 permutation17
    _ = injectiveMoment H node1172 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4499 = injectiveMoment H node579 := by
  calc
    injectiveMoment H raw4499 = injectiveMoment H raw4499step0 := by
      have heq : raw4499step0 = raw4499.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4499).symm
    injectiveMoment H raw4499step0 = injectiveMoment H raw4499step1 := by
      have heq : raw4499step1 = -raw4499step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4499step0).symm
    injectiveMoment H raw4499step1 = injectiveMoment H raw4499step2 := by
      have heq : raw4499step2 = (fun i j => raw4499step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4499step1 permutation27 permutation17
    _ = injectiveMoment H node579 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4743 = injectiveMoment H node449 := by
  calc
    injectiveMoment H raw4743 = injectiveMoment H raw4743step0 := by
      have heq : raw4743step0 = -raw4743 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4743).symm
    injectiveMoment H raw4743step0 = injectiveMoment H raw4743step1 := by
      have heq : raw4743step1 = (fun i j => raw4743step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4743step0 permutation31 permutation21
    _ = injectiveMoment H node449 := by rfl

theorem canonical4744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4744 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw4744 = injectiveMoment H raw4744step0 := by
      have heq : raw4744step0 = raw4744.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4744).symm
    injectiveMoment H raw4744step0 = injectiveMoment H raw4744step1 := by
      have heq : raw4744step1 = -raw4744step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4744step0).symm
    injectiveMoment H raw4744step1 = injectiveMoment H raw4744step2 := by
      have heq : raw4744step2 = (fun i j => raw4744step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4744step1 permutation29 permutation15
    _ = injectiveMoment H node473 := by rfl

theorem canonical4753 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4753 = injectiveMoment H node2271 := by
  calc
    injectiveMoment H raw4753 = injectiveMoment H raw4753step0 := by
      have heq : raw4753step0 = (fun i j => raw4753 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4753 permutation39 permutation9
    _ = injectiveMoment H node2271 := by rfl

theorem canonical4756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4756 = injectiveMoment H node1580 := by
  calc
    injectiveMoment H raw4756 = injectiveMoment H raw4756step0 := by
      have heq : raw4756step0 = -raw4756 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4756).symm
    injectiveMoment H raw4756step0 = injectiveMoment H raw4756step1 := by
      have heq : raw4756step1 = (fun i j => raw4756step0 (permutation145 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4756step0 permutation145 permutation21
    _ = injectiveMoment H node1580 := by rfl

theorem canonical4757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4757 = injectiveMoment H node2064 := by
  calc
    injectiveMoment H raw4757 = injectiveMoment H raw4757step0 := by
      have heq : raw4757step0 = (fun i j => raw4757 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4757 permutation33 permutation11
    _ = injectiveMoment H node2064 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4512 = injectiveMoment H node2220 := by
  rfl

theorem canonical4535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4535 = injectiveMoment H node896 := by
  calc
    injectiveMoment H raw4535 = injectiveMoment H raw4535step0 := by
      have heq : raw4535step0 = raw4535.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4535).symm
    injectiveMoment H raw4535step0 = injectiveMoment H raw4535step1 := by
      have heq : raw4535step1 = -raw4535step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4535step0).symm
    injectiveMoment H raw4535step1 = injectiveMoment H raw4535step2 := by
      have heq : raw4535step2 = (fun i j => raw4535step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4535step1 permutation27 permutation17
    _ = injectiveMoment H node896 := by rfl

theorem canonical4536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4536 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw4536 = injectiveMoment H raw4536step0 := by
      have heq : raw4536step0 = raw4536.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4536).symm
    injectiveMoment H raw4536step0 = injectiveMoment H raw4536step1 := by
      have heq : raw4536step1 = -raw4536step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4536step0).symm
    injectiveMoment H raw4536step1 = injectiveMoment H raw4536step2 := by
      have heq : raw4536step2 = (fun i j => raw4536step1 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4536step1 permutation27 permutation17
    _ = injectiveMoment H node1208 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound34
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2220 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2220 = Sparse.eval value2220 (momentVector H) := by
  have heq : pivotMatrix2220 = (fun u v => node2220 (pivotPermutation2220 u) v) := by apply Matrix.ext; unfold pivotMatrix2220 node2220 pivotPermutation2220; decide +kernel
  have hmoment : injectiveMoment H node2220 = injectiveMoment H pivotMatrix2220 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2220 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2220 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2220 (0 : Fin 4)) =
      Sparse.eval value1172 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (0 : Fin 4) = raw4344 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4344; decide +kernel
    rw [heq]
    exact (canonical4344 hH).trans (sound1172 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2220 (1 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (1 : Fin 4) = raw4499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4499; decide +kernel
    rw [heq]
    exact (canonical4499 hH).trans (sound579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2220 (2 : Fin 4)) =
      Sparse.eval value896 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (2 : Fin 4) = raw4535 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4535; decide +kernel
    rw [heq]
    exact (canonical4535 hH).trans (sound896 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2220 (3 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2220 (3 : Fin 4) = raw4536 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2220 raw4536; decide +kernel
    rw [heq]
    exact (canonical4536 hH).trans (sound1208 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2220 + (injectiveMoment H (mergeFirst pivotMatrix2220 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2220 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2220, value1172, value1208, value579, value896, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound32
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2064 = Sparse.eval value2064 (momentVector H) := by
  have heq : pivotMatrix2064 = (fun u v => node2064 (pivotPermutation2064 u) v) := by apply Matrix.ext; unfold pivotMatrix2064 node2064 pivotPermutation2064; decide +kernel
  have hmoment : injectiveMoment H node2064 = injectiveMoment H pivotMatrix2064 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2064 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2064 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2064 (0 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2064 (0 : Fin 4) = raw2188 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2064 raw2188; decide +kernel
    rw [heq]
    exact (canonical2188 hH).trans (sound1208 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2064 (1 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2064 (1 : Fin 4) = raw3661 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2064 raw3661; decide +kernel
    rw [heq]
    exact (canonical3661 hH).trans (sound473 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2064 (2 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2064 (2 : Fin 4) = raw3707 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2064 raw3707; decide +kernel
    rw [heq]
    exact (canonical3707 hH).trans (sound945 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2064 (3 : Fin 4)) =
      Sparse.eval value1009 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2064 (3 : Fin 4) = raw3710 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2064 raw3710; decide +kernel
    rw [heq]
    exact (canonical3710 hH).trans (sound1009 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2064 + (injectiveMoment H (mergeFirst pivotMatrix2064 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2064 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2064 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2064 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2064, value1009, value1208, value473, value945, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4722 = injectiveMoment H node692 := by
  rfl

theorem canonical4726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4726 = injectiveMoment H node2271 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound35
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2271 = Sparse.eval value2271 (momentVector H) := by
  have heq : pivotMatrix2271 = (fun u v => node2271 (pivotPermutation2271 u) v) := by apply Matrix.ext; unfold pivotMatrix2271 node2271 pivotPermutation2271; decide +kernel
  have hmoment : injectiveMoment H node2271 = injectiveMoment H pivotMatrix2271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2271 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2271 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2271 (0 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (0 : Fin 4) = raw4499 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4499; decide +kernel
    rw [heq]
    exact (canonical4499 hH).trans (sound579 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2271 (1 : Fin 4)) =
      Sparse.eval value692 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (1 : Fin 4) = raw4722 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4722; decide +kernel
    rw [heq]
    exact (canonical4722 hH).trans (sound692 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2271 (2 : Fin 4)) =
      Sparse.eval value449 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (2 : Fin 4) = raw4743 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4743; decide +kernel
    rw [heq]
    exact (canonical4743 hH).trans (sound449 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2271 (3 : Fin 4)) =
      Sparse.eval value473 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2271 (3 : Fin 4) = raw4744 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2271 raw4744; decide +kernel
    rw [heq]
    exact (canonical4744 hH).trans (sound473 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2271 + (injectiveMoment H (mergeFirst pivotMatrix2271 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2271 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2271, value449, value473, value579, value692, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound51
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3287 = Sparse.eval value3287 (momentVector H) := by
  have heq : pivotMatrix3287 = (fun u v => node3287 (pivotPermutation3287 u) v) := by apply Matrix.ext; unfold pivotMatrix3287 node3287 pivotPermutation3287; decide +kernel
  have hmoment : injectiveMoment H node3287 = injectiveMoment H pivotMatrix3287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3287 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3287 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3287 (0 : Fin 5)) =
      Sparse.eval value2220 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3287 (0 : Fin 5) = raw4512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3287 raw4512; decide +kernel
    rw [heq]
    exact (canonical4512 hH).trans (sound2220 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3287 (1 : Fin 5)) =
      Sparse.eval value2271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3287 (1 : Fin 5) = raw4726 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3287 raw4726; decide +kernel
    rw [heq]
    exact (canonical4726 hH).trans (sound2271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3287 (2 : Fin 5)) =
      Sparse.eval value2271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3287 (2 : Fin 5) = raw4753 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3287 raw4753; decide +kernel
    rw [heq]
    exact (canonical4753 hH).trans (sound2271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3287 (3 : Fin 5)) =
      Sparse.eval value1580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3287 (3 : Fin 5) = raw4756 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3287 raw4756; decide +kernel
    rw [heq]
    exact (canonical4756 hH).trans (sound1580 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3287 (4 : Fin 5)) =
      Sparse.eval value2064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3287 (4 : Fin 5) = raw4757 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3287 raw4757; decide +kernel
    rw [heq]
    exact (canonical4757 hH).trans (sound2064 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3287 + (injectiveMoment H (mergeFirst pivotMatrix3287 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3287 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3287 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3287 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3287 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3287, value1580, value2064, value2220, value2271, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound364 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow364 (momentVector H) = 0 := by
  have hshape : boundaryMatrix364 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix364 3 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix364 (0 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (0 : Fin 6) = raw8319 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8319 hH).trans (sound3300_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix364 (1 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (1 : Fin 6) = raw9206 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9206 hH).trans (sound3300_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix364 (2 : Fin 6)) =
      Sparse.eval value3300 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (2 : Fin 6) = raw9253 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9253 hH).trans (sound3300_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix364 (3 : Fin 6)) =
      Sparse.eval value3287 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (3 : Fin 6) = raw9269 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9269 hH).trans (sound3287 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix364 (4 : Fin 6)) =
      Sparse.eval value3351 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (4 : Fin 6) = raw9272 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9272 hH).trans (sound3351_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix364 (5 : Fin 6)) =
      Sparse.eval value3467 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix364 (5 : Fin 6) = raw9275 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9275 hH).trans (sound3467_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix364 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix364 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow364, value3287, value3300, value3351, value3467, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck199 : Integer.Sparse.reindex coordinateMap (PairData.rows 199) =
    PairSemantics.boundaryRow364 := by decide +kernel

theorem rowSound199_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 199) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck199]
  exact PairSemantics.boundarySound364 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e_oai
