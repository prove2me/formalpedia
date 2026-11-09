-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T13:58:09.760727+00:00
-- url     : https://prove2.me/submissions/6af06794-35b1-440f-a93c-9e573b5fa783

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2382_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2671_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8170 = injectiveMoment H node256 := by
  calc
    injectiveMoment H raw8170 = injectiveMoment H raw8170step0 := by
      have heq : raw8170step0 = (fun i j => raw8170 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8170 permutation15 permutation4
    _ = injectiveMoment H node256 := by rfl

theorem canonical8171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8171 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw8171 = injectiveMoment H raw8171step0 := by
      have hz : ∀ i, raw8171 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8171step0 = (fun i j => raw8171 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8171 permutation3 hz
    injectiveMoment H raw8171step0 = injectiveMoment H raw8171step1 := by
      have heq : raw8171step1 = (fun i j => raw8171step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8171step0 permutation7 permutation2
    _ = injectiveMoment H node9 := by rfl

theorem canonical8188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8188 = injectiveMoment H node2672 := by
  calc
    injectiveMoment H raw8188 = injectiveMoment H raw8188step0 := by
      have heq : raw8188step0 = (fun i j => raw8188 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8188 permutation294 permutation3
    _ = injectiveMoment H node2672 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8546 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8546 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw8546 = injectiveMoment H raw8546step0 := by
      have heq : raw8546step0 = (fun i j => raw8546 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8546 permutation15 permutation4
    _ = injectiveMoment H node272 := by rfl

theorem canonical8547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8547 = injectiveMoment H node255 := by
  calc
    injectiveMoment H raw8547 = injectiveMoment H raw8547step0 := by
      have heq : raw8547step0 = (fun i j => raw8547 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8547 permutation15 permutation4
    _ = injectiveMoment H node255 := by rfl

theorem canonical8548 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8548 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw8548 = injectiveMoment H raw8548step0 := by
      have hz : ∀ i, raw8548 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8548step0 = (fun i j => raw8548 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8548 permutation3 hz
    injectiveMoment H raw8548step0 = injectiveMoment H raw8548step1 := by
      have heq : raw8548step1 = (fun i j => raw8548step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8548step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

theorem canonical8560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8560 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8560 = injectiveMoment H raw8560step0 := by
      have hz : ∀ i, raw8560 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8560step0 = (fun i j => raw8560 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8560 permutation3 hz
    injectiveMoment H raw8560step0 = injectiveMoment H raw8560step1 := by
      have heq : raw8560step1 = (fun i j => raw8560step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8560step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical8565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8565 = injectiveMoment H node2672 := by
  calc
    injectiveMoment H raw8565 = injectiveMoment H raw8565step0 := by
      have heq : raw8565step0 = (fun i j => raw8565 (permutation298 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8565 permutation298 permutation3
    _ = injectiveMoment H node2672 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8658 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8658 = injectiveMoment H raw8658step0 := by
      have heq : raw8658step0 = (fun i j => raw8658 (permutation396 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8658 permutation396 permutation4
    _ = injectiveMoment H node2382 := by rfl

theorem canonical8664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8664 = injectiveMoment H node2382 := by
  calc
    injectiveMoment H raw8664 = injectiveMoment H raw8664step0 := by
      have heq : raw8664step0 = (fun i j => raw8664 (permutation395 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8664 permutation395 permutation4
    _ = injectiveMoment H node2382 := by rfl

theorem canonical8670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8670 = injectiveMoment H node2475 := by
  calc
    injectiveMoment H raw8670 = injectiveMoment H raw8670step0 := by
      have heq : raw8670step0 = (fun i j => raw8670 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8670 permutation294 permutation3
    _ = injectiveMoment H node2475 := by rfl

theorem canonical8671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8671 = injectiveMoment H node2671 := by
  calc
    injectiveMoment H raw8671 = injectiveMoment H raw8671step0 := by
      have heq : raw8671step0 = (fun i j => raw8671 (permutation294 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8671 permutation294 permutation3
    _ = injectiveMoment H node2671 := by rfl

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

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6758 = injectiveMoment H node1143 := by
  rfl

theorem canonical6759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6759 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6759 = injectiveMoment H raw6759step0 := by
      have heq : raw6759step0 = -raw6759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6759).symm
    injectiveMoment H raw6759step0 = injectiveMoment H raw6759step1 := by
      have heq : raw6759step1 = (fun i j => raw6759step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6759step0 permutation32 permutation3
    _ = injectiveMoment H node212 := by rfl

theorem canonical6763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6763 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6763 = injectiveMoment H raw6763step0 := by
      have heq : raw6763step0 = (fun i j => raw6763 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6763 permutation16 permutation4
    _ = injectiveMoment H node261 := by rfl

theorem canonical6765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6765 = injectiveMoment H node1144 := by
  rfl

theorem canonical6766 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6766 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw6766 = injectiveMoment H raw6766step0 := by
      have heq : raw6766step0 = -raw6766 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6766).symm
    injectiveMoment H raw6766step0 = injectiveMoment H raw6766step1 := by
      have heq : raw6766step1 = (fun i j => raw6766step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6766step0 permutation32 permutation3
    _ = injectiveMoment H node213 := by rfl

theorem canonical6767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6767 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw6767 = injectiveMoment H raw6767step0 := by
      have heq : raw6767step0 = (fun i j => raw6767 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6767 permutation58 permutation4
    _ = injectiveMoment H node743 := by rfl

theorem canonical6768 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6768 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw6768 = injectiveMoment H raw6768step0 := by
      have heq : raw6768step0 = (fun i j => raw6768 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6768 permutation57 permutation4
    _ = injectiveMoment H node743 := by rfl

theorem canonical6770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6770 = injectiveMoment H node245 := by
  calc
    injectiveMoment H raw6770 = injectiveMoment H raw6770step0 := by
      have heq : raw6770step0 = (fun i j => raw6770 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6770 permutation16 permutation4
    _ = injectiveMoment H node245 := by rfl

theorem canonical6773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6773 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw6773 = injectiveMoment H raw6773step0 := by
      have heq : raw6773step0 = -raw6773 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6773).symm
    injectiveMoment H raw6773step0 = injectiveMoment H raw6773step1 := by
      have heq : raw6773step1 = (fun i j => raw6773step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6773step0 permutation8 permutation3
    _ = injectiveMoment H node49 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical34 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw34 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw34 = injectiveMoment H raw34step0 := by
      have heq : raw34step0 = raw34.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw34).symm
    _ = injectiveMoment H node7 := by rfl

theorem canonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw35 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw35 = injectiveMoment H raw35step0 := by
      have heq : raw35step0 = raw35.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw35).symm
    injectiveMoment H raw35step0 = injectiveMoment H raw35step1 := by
      have heq : raw35step1 = (fun i j => raw35step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw35step0 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

theorem canonical53 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw53 = injectiveMoment H node1 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

theorem canonical5469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5469 = injectiveMoment H node236 := by
  rfl

theorem canonical5470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5470 = injectiveMoment H node29 := by
  calc
    injectiveMoment H raw5470 = injectiveMoment H raw5470step0 := by
      have heq : raw5470step0 = raw5470.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5470).symm
    injectiveMoment H raw5470step0 = injectiveMoment H raw5470step1 := by
      have heq : raw5470step1 = (fun i j => raw5470step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5470step0 permutation8 permutation8
    _ = injectiveMoment H node29 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5485 = injectiveMoment H node50 := by
  rfl

theorem canonical5487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5487 = injectiveMoment H node6 := by
  calc
    injectiveMoment H raw5487 = injectiveMoment H raw5487step0 := by
      have heq : raw5487step0 = raw5487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5487).symm
    injectiveMoment H raw5487step0 = injectiveMoment H raw5487step1 := by
      have heq : raw5487step1 = (fun i j => raw5487step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5487step0 permutation7 permutation2
    _ = injectiveMoment H node6 := by rfl

theorem canonical5497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5497 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw5497 = injectiveMoment H raw5497step0 := by
      have heq : raw5497step0 = -raw5497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5497).symm
    injectiveMoment H raw5497step0 = injectiveMoment H raw5497step1 := by
      have heq : raw5497step1 = (fun i j => raw5497step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5497step0 permutation32 permutation3
    _ = injectiveMoment H node225 := by rfl

theorem canonical5500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5500 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw5500 = injectiveMoment H raw5500step0 := by
      have heq : raw5500step0 = (fun i j => raw5500 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5500 permutation10 permutation3
    _ = injectiveMoment H node246 := by rfl

theorem canonical5501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5501 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw5501 = injectiveMoment H raw5501step0 := by
      have heq : raw5501step0 = -raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5501).symm
    injectiveMoment H raw5501step0 = injectiveMoment H raw5501step1 := by
      have heq : raw5501step1 = (fun i j => raw5501step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5501step0 permutation8 permutation3
    _ = injectiveMoment H node40 := by rfl

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

theorem canonical5540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5540 = injectiveMoment H node51 := by
  rfl

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

theorem canonical5552 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5552 = injectiveMoment H node54 := by
  rfl

theorem canonical5555 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5555 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw5555 = injectiveMoment H raw5555step0 := by
      have heq : raw5555step0 = (fun i j => raw5555 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5555 permutation4 permutation3
    _ = injectiveMoment H node52 := by rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical5984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5984 = injectiveMoment H node266 := by
  calc
    injectiveMoment H raw5984 = injectiveMoment H raw5984step0 := by
      have heq : raw5984step0 = (fun i j => raw5984 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5984 permutation11 permutation3
    _ = injectiveMoment H node266 := by rfl

theorem canonical5988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5988 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw5988 = injectiveMoment H raw5988step0 := by
      have heq : raw5988step0 = (fun i j => raw5988 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5988 permutation4 permutation3
    _ = injectiveMoment H node59 := by rfl

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

theorem canonical6880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6880 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw6880 = injectiveMoment H raw6880step0 := by
      have heq : raw6880step0 = (fun i j => raw6880 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6880 permutation4 permutation3
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7983 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7983 = injectiveMoment H raw7983step0 := by
      have heq : raw7983step0 = (fun i j => raw7983 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7983 permutation17 permutation4
    _ = injectiveMoment H node281 := by rfl

theorem canonical7984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7984 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7984 = injectiveMoment H raw7984step0 := by
      have heq : raw7984step0 = -raw7984 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7984).symm
    injectiveMoment H raw7984step0 = injectiveMoment H raw7984step1 := by
      have heq : raw7984step1 = (fun i j => raw7984step0 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7984step0 permutation7 permutation3
    _ = injectiveMoment H node59 := by rfl

theorem canonical7985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7985 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7985 = injectiveMoment H raw7985step0 := by
      have heq : raw7985step0 = (fun i j => raw7985 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7985 permutation5 permutation4
    _ = injectiveMoment H node59 := by rfl

theorem canonical7986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7986 = injectiveMoment H node54 := by
  calc
    injectiveMoment H raw7986 = injectiveMoment H raw7986step0 := by
      have heq : raw7986step0 = (fun i j => raw7986 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7986 permutation5 permutation4
    _ = injectiveMoment H node54 := by rfl

theorem canonical7987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7987 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw7987 = injectiveMoment H raw7987step0 := by
      have hz : ∀ i, raw7987 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7987step0 = (fun i j => raw7987 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7987 permutation3 hz
    _ = injectiveMoment H node9 := by rfl

theorem canonical7988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7988 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw7988 = injectiveMoment H raw7988step0 := by
      have hz : ∀ i, raw7988 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw7988step0 = (fun i j => raw7988 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7988 permutation3 hz
    _ = injectiveMoment H node2 := by rfl

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

theorem canonical7996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7996 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7996 = injectiveMoment H raw7996step0 := by
      have heq : raw7996step0 = (fun i j => raw7996 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7996 permutation5 permutation4
    _ = injectiveMoment H node58 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

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

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw182 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw182 = injectiveMoment H raw182step0 := by
      have heq : raw182step0 = raw182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw182).symm
    injectiveMoment H raw182step0 = injectiveMoment H raw182step1 := by
      have heq : raw182step1 = (fun i j => raw182step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw182step0 permutation4 permutation1
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound1 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1 = Sparse.eval value1 (momentVector H) := by
  have hc : momentVector H 58 = injectiveMoment H node1 := rfl
  simp [value1, Sparse.eval, hc]

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound6 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node6 = Sparse.eval value6 (momentVector H) := by
  have heq : pivotMatrix6 = (fun u v => node6 (pivotPermutation6 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node6 = injectiveMoment H pivotMatrix6 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix6 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix6 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (0 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)) =
      Sparse.eval value1 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (1 : Fin 2) = raw53 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical53 hH).trans (sound1 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node6 + (injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value6, value1, value2, Sparse.eval] at hc ⊢
  linarith

theorem sound7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node7 = Sparse.eval value7 (momentVector H) := by
  have hc : momentVector H 9 = injectiveMoment H node7 := rfl
  simp [value7, Sparse.eval, hc]

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
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

theorem sound29 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node29 = Sparse.eval value29 (momentVector H) := by
  have hc : momentVector H 278 = injectiveMoment H node29 := rfl
  simp [value29, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound48 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node48 = Sparse.eval value48 (momentVector H) := by
  have heq : pivotMatrix48 = (fun u v => node48.transpose (pivotPermutation48 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node48 = injectiveMoment H pivotMatrix48 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix48 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix48 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (0 : Fin 2) = raw34 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical34 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix48 (1 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node48 + (injectiveMoment H (mergeFirst pivotMatrix48 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix48 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value48, value7, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound49 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node49 = Sparse.eval value49 (momentVector H) := by
  have heq : pivotMatrix49 = (fun u v => node49.transpose (pivotPermutation49 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node49 = injectiveMoment H pivotMatrix49 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix49 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix49 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (0 : Fin 2) = raw35 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical35 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (1 : Fin 2) = raw182 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical182 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node49 + (injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value49, value7, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound50 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node50 = Sparse.eval value50 (momentVector H) := by
  have heq : pivotMatrix50 = (fun u v => node50 (pivotPermutation50 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node50 = injectiveMoment H pivotMatrix50 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix50 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix50 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix50 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix50 (0 : Fin 2) = raw7988 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7988 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix50 (1 : Fin 2)) =
      Sparse.eval value6 (momentVector H) := by
    have heq : mergeFirst pivotMatrix50 (1 : Fin 2) = raw5487 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5487 hH).trans (sound6 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node50 + (injectiveMoment H (mergeFirst pivotMatrix50 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix50 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value50, value2, value6, Sparse.eval] at hc ⊢
  linarith

theorem sound51 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node51 = Sparse.eval value51 (momentVector H) := by
  have heq : pivotMatrix51 = (fun u v => node51 (pivotPermutation51 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node51 = injectiveMoment H pivotMatrix51 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix51 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix51 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (0 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node51 + (injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value51, value10, value8, Sparse.eval] at hc ⊢
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

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound54 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node54 = Sparse.eval value54 (momentVector H) := by
  have heq : pivotMatrix54 = (fun u v => node54 (pivotPermutation54 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node54 = injectiveMoment H pivotMatrix54 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix54 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix54 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (0 : Fin 2) = raw7988 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7988 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix54 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node54 + (injectiveMoment H (mergeFirst pivotMatrix54 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix54 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value54, value2, value8, Sparse.eval] at hc ⊢
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

theorem sound58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node58 = Sparse.eval value58 (momentVector H) := by
  have heq : pivotMatrix58 = (fun u v => node58 (pivotPermutation58 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node58 = injectiveMoment H pivotMatrix58 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix58 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix58 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node58 + (injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value58, value10, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
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

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5505 = injectiveMoment H node247 := by
  rfl

theorem canonical5506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5506 = injectiveMoment H node248 := by
  rfl

theorem canonical5507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5507 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw5507 = injectiveMoment H raw5507step0 := by
      have heq : raw5507step0 = raw5507.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5507).symm
    injectiveMoment H raw5507step0 = injectiveMoment H raw5507step1 := by
      have heq : raw5507step1 = (fun i j => raw5507step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5507step0 permutation8 permutation8
    _ = injectiveMoment H node32 := by rfl

theorem canonical5508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5508 = injectiveMoment H node745 := by
  rfl

theorem canonical5509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5509 = injectiveMoment H node249 := by
  rfl

theorem canonical5510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5510 = injectiveMoment H node249 := by
  calc
    injectiveMoment H raw5510 = injectiveMoment H raw5510step0 := by
      have heq : raw5510step0 = (fun i j => raw5510 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5510 permutation10 permutation3
    _ = injectiveMoment H node249 := by rfl

theorem canonical5511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5511 = injectiveMoment H node42 := by
  calc
    injectiveMoment H raw5511 = injectiveMoment H raw5511step0 := by
      have heq : raw5511step0 = -raw5511 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5511).symm
    injectiveMoment H raw5511step0 = injectiveMoment H raw5511step1 := by
      have heq : raw5511step1 = (fun i j => raw5511step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5511step0 permutation8 permutation3
    _ = injectiveMoment H node42 := by rfl

theorem canonical5534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5534 = injectiveMoment H node254 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5889 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5889 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw5889 = injectiveMoment H raw5889step0 := by
      have heq : raw5889step0 = (fun i j => raw5889 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5889 permutation12 permutation5
    _ = injectiveMoment H node176 := by rfl

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

theorem canonical5895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5895 = injectiveMoment H node876 := by
  rfl

theorem canonical5900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5900 = injectiveMoment H node263 := by
  rfl

theorem canonical5901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5901 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw5901 = injectiveMoment H raw5901step0 := by
      have heq : raw5901step0 = (fun i j => raw5901 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5901 permutation10 permutation3
    _ = injectiveMoment H node263 := by rfl

theorem canonical5902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5902 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw5902 = injectiveMoment H raw5902step0 := by
      have heq : raw5902step0 = -raw5902 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5902).symm
    injectiveMoment H raw5902step0 = injectiveMoment H raw5902step1 := by
      have heq : raw5902step1 = (fun i j => raw5902step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5902step0 permutation8 permutation3
    _ = injectiveMoment H node43 := by rfl

theorem canonical5903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5903 = injectiveMoment H node877 := by
  rfl

theorem canonical5904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5904 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw5904 = injectiveMoment H raw5904step0 := by
      have heq : raw5904step0 = -raw5904 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5904).symm
    injectiveMoment H raw5904step0 = injectiveMoment H raw5904step1 := by
      have heq : raw5904step1 = (fun i j => raw5904step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5904step0 permutation32 permutation3
    _ = injectiveMoment H node211 := by rfl

theorem canonical5905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5905 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5905 = injectiveMoment H raw5905step0 := by
      have heq : raw5905step0 = (fun i j => raw5905 (permutation58 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5905 permutation58 permutation4
    _ = injectiveMoment H node744 := by rfl

theorem canonical5906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5906 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5906 = injectiveMoment H raw5906step0 := by
      have heq : raw5906step0 = (fun i j => raw5906 (permutation57 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5906 permutation57 permutation4
    _ = injectiveMoment H node744 := by rfl

theorem canonical5907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5907 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw5907 = injectiveMoment H raw5907step0 := by
      have heq : raw5907step0 = (fun i j => raw5907 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5907 permutation16 permutation4
    _ = injectiveMoment H node247 := by rfl

theorem canonical5916 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5916 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw5916 = injectiveMoment H raw5916step0 := by
      have heq : raw5916step0 = -raw5916 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5916).symm
    injectiveMoment H raw5916step0 = injectiveMoment H raw5916step1 := by
      have heq : raw5916step1 = (fun i j => raw5916step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5916step0 permutation8 permutation3
    _ = injectiveMoment H node48 := by rfl

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

theorem canonical5982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5982 = injectiveMoment H node58 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

theorem canonical6867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6867 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw6867 = injectiveMoment H raw6867step0 := by
      have heq : raw6867step0 = (fun i j => raw6867 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6867 permutation11 permutation3
    _ = injectiveMoment H node280 := by rfl

theorem canonical6873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6873 = injectiveMoment H node278 := by
  calc
    injectiveMoment H raw6873 = injectiveMoment H raw6873step0 := by
      have heq : raw6873step0 = (fun i j => raw6873 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6873 permutation11 permutation3
    _ = injectiveMoment H node278 := by rfl

theorem canonical6877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6877 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6877 = injectiveMoment H raw6877step0 := by
      have heq : raw6877step0 = -raw6877 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6877).symm
    injectiveMoment H raw6877step0 = injectiveMoment H raw6877step1 := by
      have heq : raw6877step1 = (fun i j => raw6877step0 (permutation6 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6877step0 permutation6 permutation4
    _ = injectiveMoment H node59 := by rfl

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

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem sound211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node211 = Sparse.eval value211 (momentVector H) := by
  have hc : momentVector H 727 = injectiveMoment H node211 := rfl
  simp [value211, Sparse.eval, hc]

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

theorem sound213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node213 = Sparse.eval value213 (momentVector H) := by
  have hc : momentVector H 728 = injectiveMoment H node213 := rfl
  simp [value213, Sparse.eval, hc]

theorem sound225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node225 = Sparse.eval value225 (momentVector H) := by
  have hc : momentVector H 228 = injectiveMoment H node225 := rfl
  simp [value225, Sparse.eval, hc]

theorem sound236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node236 = Sparse.eval value236 (momentVector H) := by
  have heq : pivotMatrix236 = (fun u v => node236 (pivotPermutation236 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node236 = injectiveMoment H pivotMatrix236 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix236 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix236 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix236 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix236 (0 : Fin 3) = raw7986 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7986 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix236 (1 : Fin 3)) =
      Sparse.eval value50 (momentVector H) := by
    have heq : mergeFirst pivotMatrix236 (1 : Fin 3) = raw5485 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5485 hH).trans (sound50 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix236 (2 : Fin 3)) =
      Sparse.eval value29 (momentVector H) := by
    have heq : mergeFirst pivotMatrix236 (2 : Fin 3) = raw5470 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5470 hH).trans (sound29 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node236 + (injectiveMoment H (mergeFirst pivotMatrix236 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix236 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix236 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value236, value29, value50, value54, Sparse.eval] at hc ⊢
  linarith

theorem sound245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node245 = Sparse.eval value245 (momentVector H) := by
  have heq : pivotMatrix245 = (fun u v => node245 (pivotPermutation245 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node245 = injectiveMoment H pivotMatrix245 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix245 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix245 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix245 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix245 (0 : Fin 3) = raw7984 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7984 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix245 (1 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix245 (1 : Fin 3) = raw5540 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix245 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix245 (2 : Fin 3) = raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5501 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node245 + (injectiveMoment H (mergeFirst pivotMatrix245 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix245 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix245 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value245, value40, value51, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node246 = Sparse.eval value246 (momentVector H) := by
  have heq : pivotMatrix246 = (fun u v => node246 (pivotPermutation246 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node246 = injectiveMoment H pivotMatrix246 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix246 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix246 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix246 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (0 : Fin 3) = raw7995 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix246 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (1 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix246 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix246 (2 : Fin 3) = raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5501 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node246 + (injectiveMoment H (mergeFirst pivotMatrix246 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix246 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix246 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value246, value40, value52, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound247 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node247 = Sparse.eval value247 (momentVector H) := by
  have heq : pivotMatrix247 = (fun u v => node247 (pivotPermutation247 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node247 = injectiveMoment H pivotMatrix247 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix247 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix247 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix247 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix247 (0 : Fin 3) = raw7985 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7985 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix247 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix247 (1 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix247 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix247 (2 : Fin 3) = raw5507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5507 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node247 + (injectiveMoment H (mergeFirst pivotMatrix247 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix247 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix247 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value247, value32, value52, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound248 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node248 = Sparse.eval value248 (momentVector H) := by
  have heq : pivotMatrix248 = (fun u v => node248 (pivotPermutation248 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node248 = injectiveMoment H pivotMatrix248 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix248 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix248 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix248 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (0 : Fin 3) = raw7996 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix248 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (1 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix248 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix248 (2 : Fin 3) = raw5507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5507 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node248 + (injectiveMoment H (mergeFirst pivotMatrix248 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix248 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix248 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value248, value32, value53, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound249 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node249 = Sparse.eval value249 (momentVector H) := by
  have heq : pivotMatrix249 = (fun u v => node249 (pivotPermutation249 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node249 = injectiveMoment H pivotMatrix249 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix249 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix249 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix249 (0 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix249 (0 : Fin 3) = raw7986 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7986 hH).trans (sound54 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix249 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix249 (1 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix249 (2 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix249 (2 : Fin 3) = raw5511 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5511 hH).trans (sound42 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node249 + (injectiveMoment H (mergeFirst pivotMatrix249 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix249 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix249 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value249, value42, value53, value54, Sparse.eval] at hc ⊢
  linarith

theorem sound254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node254 = Sparse.eval value254 (momentVector H) := by
  have heq : pivotMatrix254 = (fun u v => node254 (pivotPermutation254 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node254 = injectiveMoment H pivotMatrix254 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix254 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix254 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix254 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix254 (1 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (1 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix254 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix254 (2 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node254 + (injectiveMoment H (mergeFirst pivotMatrix254 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix254 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix254 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value254, value52, value53, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound255 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node255 = Sparse.eval value255 (momentVector H) := by
  have heq : pivotMatrix255 = (fun u v => node255 (pivotPermutation255 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node255 = injectiveMoment H pivotMatrix255 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix255 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix255 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix255 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix255 (0 : Fin 3) = raw5982 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix255 (1 : Fin 3)) =
      Sparse.eval value54 (momentVector H) := by
    have heq : mergeFirst pivotMatrix255 (1 : Fin 3) = raw5552 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5552 hH).trans (sound54 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix255 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix255 (2 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node255 + (injectiveMoment H (mergeFirst pivotMatrix255 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix255 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix255 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value255, value53, value54, value58, Sparse.eval] at hc ⊢
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

theorem sound256 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node256 = Sparse.eval value256 (momentVector H) := by
  have heq : pivotMatrix256 = (fun u v => node256 (pivotPermutation256 u) v) := by apply Matrix.ext; unfold pivotMatrix256 node256 pivotPermutation256; decide +kernel
  have hmoment : injectiveMoment H node256 = injectiveMoment H pivotMatrix256 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix256 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix256 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (0 : Fin 3) = raw7987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw7987; decide +kernel
    rw [heq]
    exact (canonical7987 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (1 : Fin 3) = raw5555 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5555; decide +kernel
    rw [heq]
    exact (canonical5555 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix256 (2 : Fin 3) = raw5547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix256 raw5547; decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node256 + (injectiveMoment H (mergeFirst pivotMatrix256 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix256 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value256, value52, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node261 = Sparse.eval value261 (momentVector H) := by
  have heq : pivotMatrix261 = (fun u v => node261 (pivotPermutation261 u) v) := by apply Matrix.ext; unfold pivotMatrix261 node261 pivotPermutation261; decide +kernel
  have hmoment : injectiveMoment H node261 = injectiveMoment H pivotMatrix261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix261 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (0 : Fin 3) = raw7995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw7995; decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (2 : Fin 3) = raw5891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5891; decide +kernel
    rw [heq]
    exact (canonical5891 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node261 + (injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value261, value36, value56, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node263 = Sparse.eval value263 (momentVector H) := by
  have heq : pivotMatrix263 = (fun u v => node263 (pivotPermutation263 u) v) := by apply Matrix.ext; unfold pivotMatrix263 node263 pivotPermutation263; decide +kernel
  have hmoment : injectiveMoment H node263 = injectiveMoment H pivotMatrix263 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix263 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix263 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (0 : Fin 3) = raw7996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw7996; decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (2 : Fin 3) = raw5902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5902; decide +kernel
    rw [heq]
    exact (canonical5902 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node263 + (injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value263, value43, value57, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound266 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node266 = Sparse.eval value266 (momentVector H) := by
  have heq : pivotMatrix266 = (fun u v => node266 (pivotPermutation266 u) v) := by apply Matrix.ext; unfold pivotMatrix266 node266 pivotPermutation266; decide +kernel
  have hmoment : injectiveMoment H node266 = injectiveMoment H pivotMatrix266 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix266 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix266 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix266 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (0 : Fin 3) = raw8171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw8171; decide +kernel
    rw [heq]
    exact (canonical8171 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix266 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (1 : Fin 3) = raw5988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw5988; decide +kernel
    rw [heq]
    exact (canonical5988 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix266 (2 : Fin 3)) =
      Sparse.eval value48 (momentVector H) := by
    have heq : mergeFirst pivotMatrix266 (2 : Fin 3) = raw5916 := by apply Matrix.ext; unfold mergeFirst pivotMatrix266 raw5916; decide +kernel
    rw [heq]
    exact (canonical5916 hH).trans (sound48 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node266 + (injectiveMoment H (mergeFirst pivotMatrix266 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix266 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix266 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value266, value48, value59, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node272 = Sparse.eval value272 (momentVector H) := by
  have heq : pivotMatrix272 = (fun u v => node272 (pivotPermutation272 u) v) := by apply Matrix.ext; unfold pivotMatrix272 node272 pivotPermutation272; decide +kernel
  have hmoment : injectiveMoment H node272 = injectiveMoment H pivotMatrix272 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix272 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix272 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (1 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix272 (2 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix272 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node272 + (injectiveMoment H (mergeFirst pivotMatrix272 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix272 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value272, value57, value58, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node278 = Sparse.eval value278 (momentVector H) := by
  have heq : pivotMatrix278 = (fun u v => node278 (pivotPermutation278 u) v) := by apply Matrix.ext; unfold pivotMatrix278 node278 pivotPermutation278; decide +kernel
  have hmoment : injectiveMoment H node278 = injectiveMoment H pivotMatrix278 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix278 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix278 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix278 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (0 : Fin 3) = raw8548 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw8548; decide +kernel
    rw [heq]
    exact (canonical8548 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix278 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (1 : Fin 3) = raw6877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw6877; decide +kernel
    rw [heq]
    exact (canonical6877 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix278 (2 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix278 (2 : Fin 3) = raw6773 := by apply Matrix.ext; unfold mergeFirst pivotMatrix278 raw6773; decide +kernel
    rw [heq]
    exact (canonical6773 hH).trans (sound49 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node278 + (injectiveMoment H (mergeFirst pivotMatrix278 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix278 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix278 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value278, value49, value59, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound280 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node280 = Sparse.eval value280 (momentVector H) := by
  have heq : pivotMatrix280 = (fun u v => node280 (pivotPermutation280 u) v) := by apply Matrix.ext; unfold pivotMatrix280 node280 pivotPermutation280; decide +kernel
  have hmoment : injectiveMoment H node280 = injectiveMoment H pivotMatrix280 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix280 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix280 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (0 : Fin 3) = raw8560 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw8560; decide +kernel
    rw [heq]
    exact (canonical8560 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (1 : Fin 3) = raw6880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6880; decide +kernel
    rw [heq]
    exact (canonical6880 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix280 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix280 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node280 + (injectiveMoment H (mergeFirst pivotMatrix280 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix280 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value280, value10, value52, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound281 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node281 = Sparse.eval value281 (momentVector H) := by
  have heq : pivotMatrix281 = (fun u v => node281 (pivotPermutation281 u) v) := by apply Matrix.ext; unfold pivotMatrix281 node281 pivotPermutation281; decide +kernel
  have hmoment : injectiveMoment H node281 = injectiveMoment H pivotMatrix281 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix281 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix281 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (0 : Fin 3) = raw8171 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw8171; decide +kernel
    rw [heq]
    exact (canonical8171 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (1 : Fin 3) = raw6877 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6877; decide +kernel
    rw [heq]
    exact (canonical6877 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix281 (2 : Fin 3) = raw6789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix281 raw6789; decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node281 + (injectiveMoment H (mergeFirst pivotMatrix281 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix281 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value281, value52, value59, value9, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node743 = Sparse.eval value743 (momentVector H) := by
  have heq : pivotMatrix743 = (fun u v => node743 (pivotPermutation743 u) v) := by apply Matrix.ext; unfold pivotMatrix743 node743 pivotPermutation743; decide +kernel
  have hmoment : injectiveMoment H node743 = injectiveMoment H pivotMatrix743 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix743 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix743 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix743 (0 : Fin 4)) =
      Sparse.eval value281 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (0 : Fin 4) = raw7983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw7983; decide +kernel
    rw [heq]
    exact (canonical7983 hH).trans (sound281 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix743 (1 : Fin 4)) =
      Sparse.eval value254 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (1 : Fin 4) = raw5534 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5534; decide +kernel
    rw [heq]
    exact (canonical5534 hH).trans (sound254 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix743 (2 : Fin 4)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (2 : Fin 4) = raw5500 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5500; decide +kernel
    rw [heq]
    exact (canonical5500 hH).trans (sound246 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix743 (3 : Fin 4)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix743 (3 : Fin 4) = raw5497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix743 raw5497; decide +kernel
    rw [heq]
    exact (canonical5497 hH).trans (sound225 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node743 + (injectiveMoment H (mergeFirst pivotMatrix743 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix743 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value743, value225, value246, value254, value281, Sparse.eval] at hc ⊢
  linarith

theorem sound744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node744 = Sparse.eval value744 (momentVector H) := by
  have heq : pivotMatrix744 = (fun u v => node744 (pivotPermutation744 u) v) := by apply Matrix.ext; unfold pivotMatrix744 node744 pivotPermutation744; decide +kernel
  have hmoment : injectiveMoment H node744 = injectiveMoment H pivotMatrix744 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix744 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix744 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix744 (0 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (0 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix744 (1 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (1 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix744 (2 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (2 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix744 (3 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix744 (3 : Fin 4) = raw5505 := by apply Matrix.ext; unfold mergeFirst pivotMatrix744 raw5505; decide +kernel
    rw [heq]
    exact (canonical5505 hH).trans (sound247 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node744 + (injectiveMoment H (mergeFirst pivotMatrix744 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix744 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value744, value247, value248, value249, value263, Sparse.eval] at hc ⊢
  linarith

theorem sound745 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node745 = Sparse.eval value745 (momentVector H) := by
  have heq : pivotMatrix745 = (fun u v => node745 (pivotPermutation745 u) v) := by apply Matrix.ext; unfold pivotMatrix745 node745 pivotPermutation745; decide +kernel
  have hmoment : injectiveMoment H node745 = injectiveMoment H pivotMatrix745 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix745 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix745 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix745 (0 : Fin 4)) =
      Sparse.eval value236 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (0 : Fin 4) = raw5469 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5469; decide +kernel
    rw [heq]
    exact (canonical5469 hH).trans (sound236 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix745 (1 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (1 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix745 (2 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (2 : Fin 4) = raw5509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5509; decide +kernel
    rw [heq]
    exact (canonical5509 hH).trans (sound249 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix745 (3 : Fin 4)) =
      Sparse.eval value249 (momentVector H) := by
    have heq : mergeFirst pivotMatrix745 (3 : Fin 4) = raw5510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix745 raw5510; decide +kernel
    rw [heq]
    exact (canonical5510 hH).trans (sound249 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node745 + (injectiveMoment H (mergeFirst pivotMatrix745 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix745 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value745, value236, value248, value249, Sparse.eval] at hc ⊢
  linarith

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

theorem sound876 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node876 = Sparse.eval value876 (momentVector H) := by
  have heq : pivotMatrix876 = (fun u v => node876 (pivotPermutation876 u) v) := by apply Matrix.ext; unfold pivotMatrix876 node876 pivotPermutation876; decide +kernel
  have hmoment : injectiveMoment H node876 = injectiveMoment H pivotMatrix876 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix876 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix876 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix876 (0 : Fin 4)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (0 : Fin 4) = raw5506 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5506; decide +kernel
    rw [heq]
    exact (canonical5506 hH).trans (sound248 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix876 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (1 : Fin 4) = raw5889 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5889; decide +kernel
    rw [heq]
    exact (canonical5889 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix876 (2 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (2 : Fin 4) = raw5900 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5900; decide +kernel
    rw [heq]
    exact (canonical5900 hH).trans (sound263 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix876 (3 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix876 (3 : Fin 4) = raw5901 := by apply Matrix.ext; unfold mergeFirst pivotMatrix876 raw5901; decide +kernel
    rw [heq]
    exact (canonical5901 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node876 + (injectiveMoment H (mergeFirst pivotMatrix876 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix876 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value876, value176, value248, value263, Sparse.eval] at hc ⊢
  linarith

theorem sound877 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node877 = Sparse.eval value877 (momentVector H) := by
  have heq : pivotMatrix877 = (fun u v => node877 (pivotPermutation877 u) v) := by apply Matrix.ext; unfold pivotMatrix877 node877 pivotPermutation877; decide +kernel
  have hmoment : injectiveMoment H node877 = injectiveMoment H pivotMatrix877 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix877 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix877 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix877 (0 : Fin 4)) =
      Sparse.eval value256 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (0 : Fin 4) = raw8170 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw8170; decide +kernel
    rw [heq]
    exact (canonical8170 hH).trans (sound256 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix877 (1 : Fin 4)) =
      Sparse.eval value266 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (1 : Fin 4) = raw5984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5984; decide +kernel
    rw [heq]
    exact (canonical5984 hH).trans (sound266 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix877 (2 : Fin 4)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (2 : Fin 4) = raw5907 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5907; decide +kernel
    rw [heq]
    exact (canonical5907 hH).trans (sound247 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix877 (3 : Fin 4)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix877 (3 : Fin 4) = raw5904 := by apply Matrix.ext; unfold mergeFirst pivotMatrix877 raw5904; decide +kernel
    rw [heq]
    exact (canonical5904 hH).trans (sound211 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node877 + (injectiveMoment H (mergeFirst pivotMatrix877 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix877 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value877, value211, value247, value256, value266, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound17
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1143 = Sparse.eval value1143 (momentVector H) := by
  have heq : pivotMatrix1143 = (fun u v => node1143 (pivotPermutation1143 u) v) := by apply Matrix.ext; unfold pivotMatrix1143 node1143 pivotPermutation1143; decide +kernel
  have hmoment : injectiveMoment H node1143 = injectiveMoment H pivotMatrix1143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1143 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1143 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1143 (0 : Fin 4)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (0 : Fin 4) = raw8546 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw8546; decide +kernel
    rw [heq]
    exact (canonical8546 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1143 (1 : Fin 4)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (1 : Fin 4) = raw6867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6867; decide +kernel
    rw [heq]
    exact (canonical6867 hH).trans (sound280 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1143 (2 : Fin 4)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (2 : Fin 4) = raw6763 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6763; decide +kernel
    rw [heq]
    exact (canonical6763 hH).trans (sound261 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1143 (3 : Fin 4)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1143 (3 : Fin 4) = raw6759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1143 raw6759; decide +kernel
    rw [heq]
    exact (canonical6759 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1143 + (injectiveMoment H (mergeFirst pivotMatrix1143 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1143 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1143, value212, value261, value272, value280, Sparse.eval] at hc ⊢
  linarith

theorem sound1144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1144 = Sparse.eval value1144 (momentVector H) := by
  have heq : pivotMatrix1144 = (fun u v => node1144 (pivotPermutation1144 u) v) := by apply Matrix.ext; unfold pivotMatrix1144 node1144 pivotPermutation1144; decide +kernel
  have hmoment : injectiveMoment H node1144 = injectiveMoment H pivotMatrix1144 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1144 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1144 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1144 (0 : Fin 4)) =
      Sparse.eval value255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (0 : Fin 4) = raw8547 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw8547; decide +kernel
    rw [heq]
    exact (canonical8547 hH).trans (sound255 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1144 (1 : Fin 4)) =
      Sparse.eval value278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (1 : Fin 4) = raw6873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6873; decide +kernel
    rw [heq]
    exact (canonical6873 hH).trans (sound278 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1144 (2 : Fin 4)) =
      Sparse.eval value245 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (2 : Fin 4) = raw6770 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6770; decide +kernel
    rw [heq]
    exact (canonical6770 hH).trans (sound245 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1144 (3 : Fin 4)) =
      Sparse.eval value213 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1144 (3 : Fin 4) = raw6766 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1144 raw6766; decide +kernel
    rw [heq]
    exact (canonical6766 hH).trans (sound213 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1144 + (injectiveMoment H (mergeFirst pivotMatrix1144 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1144 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1144, value213, value245, value255, value278, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound38
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2475 = Sparse.eval value2475 (momentVector H) := by
  have heq : pivotMatrix2475 = (fun u v => node2475 (pivotPermutation2475 u) v) := by apply Matrix.ext; unfold pivotMatrix2475 node2475 pivotPermutation2475; decide +kernel
  have hmoment : injectiveMoment H node2475 = injectiveMoment H pivotMatrix2475 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2475 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2475 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2475 (0 : Fin 5)) =
      Sparse.eval value745 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (0 : Fin 5) = raw5508 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5508; decide +kernel
    rw [heq]
    exact (canonical5508 hH).trans (sound745 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2475 (1 : Fin 5)) =
      Sparse.eval value876 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (1 : Fin 5) = raw5895 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5895; decide +kernel
    rw [heq]
    exact (canonical5895 hH).trans (sound876 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2475 (2 : Fin 5)) =
      Sparse.eval value877 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (2 : Fin 5) = raw5903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5903; decide +kernel
    rw [heq]
    exact (canonical5903 hH).trans (sound877 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2475 (3 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (3 : Fin 5) = raw5905 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5905; decide +kernel
    rw [heq]
    exact (canonical5905 hH).trans (sound744 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2475 (4 : Fin 5)) =
      Sparse.eval value744 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2475 (4 : Fin 5) = raw5906 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2475 raw5906; decide +kernel
    rw [heq]
    exact (canonical5906 hH).trans (sound744 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2475 + (injectiveMoment H (mergeFirst pivotMatrix2475 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2475 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2475, value744, value745, value876, value877, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound41
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2672 = Sparse.eval value2672 (momentVector H) := by
  have heq : pivotMatrix2672 = (fun u v => node2672 (pivotPermutation2672 u) v) := by apply Matrix.ext; unfold pivotMatrix2672 node2672 pivotPermutation2672; decide +kernel
  have hmoment : injectiveMoment H node2672 = injectiveMoment H pivotMatrix2672 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2672 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2672 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2672 (0 : Fin 5)) =
      Sparse.eval value877 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (0 : Fin 5) = raw5903 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw5903; decide +kernel
    rw [heq]
    exact (canonical5903 hH).trans (sound877 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2672 (1 : Fin 5)) =
      Sparse.eval value1143 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (1 : Fin 5) = raw6758 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6758; decide +kernel
    rw [heq]
    exact (canonical6758 hH).trans (sound1143 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2672 (2 : Fin 5)) =
      Sparse.eval value1144 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (2 : Fin 5) = raw6765 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6765; decide +kernel
    rw [heq]
    exact (canonical6765 hH).trans (sound1144 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2672 (3 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (3 : Fin 5) = raw6767 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6767; decide +kernel
    rw [heq]
    exact (canonical6767 hH).trans (sound743 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2672 (4 : Fin 5)) =
      Sparse.eval value743 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2672 (4 : Fin 5) = raw6768 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2672 raw6768; decide +kernel
    rw [heq]
    exact (canonical6768 hH).trans (sound743 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2672 + (injectiveMoment H (mergeFirst pivotMatrix2672 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2672 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2672, value1143, value1144, value743, value877, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound243 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow243 (momentVector H) = 0 := by
  have hshape : boundaryMatrix243 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix243 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix243 (0 : Fin 6)) =
      Sparse.eval value2672 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (0 : Fin 6) = raw8188 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8188 hH).trans (sound2672 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix243 (1 : Fin 6)) =
      Sparse.eval value2672 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (1 : Fin 6) = raw8565 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8565 hH).trans (sound2672 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix243 (2 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (2 : Fin 6) = raw8658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8658 hH).trans (sound2382_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix243 (3 : Fin 6)) =
      Sparse.eval value2382 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (3 : Fin 6) = raw8664 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8664 hH).trans (sound2382_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix243 (4 : Fin 6)) =
      Sparse.eval value2475 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (4 : Fin 6) = raw8670 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8670 hH).trans (sound2475 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix243 (5 : Fin 6)) =
      Sparse.eval value2671 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix243 (5 : Fin 6) = raw8671 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8671 hH).trans (sound2671_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix243 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix243 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow243, value2382, value2475, value2671, value2672, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck138 : Integer.Sparse.reindex coordinateMap (PairData.rows 138) =
    PairSemantics.boundaryRow243 := by decide +kernel

theorem rowSound138_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 138) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck138]
  exact PairSemantics.boundarySound243 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e_oai
