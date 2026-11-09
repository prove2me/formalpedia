-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T14:36:31.922328+00:00
-- url     : https://prove2.me/submissions/3a0d0e75-96cd-42e1-9f5f-d48462d7602b

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2880_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2979_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3120_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9106 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9106 = injectiveMoment H node3121 := by
  calc
    injectiveMoment H raw9106 = injectiveMoment H raw9106step0 := by
      have heq : raw9106step0 = -raw9106 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9106).symm
    injectiveMoment H raw9106step0 = injectiveMoment H raw9106step1 := by
      have heq : raw9106step1 = (fun i j => raw9106step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9106step0 permutation335 permutation15
    _ = injectiveMoment H node3121 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9235 = injectiveMoment H node3121 := by
  calc
    injectiveMoment H raw9235 = injectiveMoment H raw9235step0 := by
      have heq : raw9235step0 = -raw9235 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9235).symm
    injectiveMoment H raw9235step0 = injectiveMoment H raw9235step1 := by
      have heq : raw9235step1 = (fun i j => raw9235step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9235step0 permutation312 permutation15
    _ = injectiveMoment H node3121 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical292
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9351 = injectiveMoment H node3120 := by
  calc
    injectiveMoment H raw9351 = injectiveMoment H raw9351step0 := by
      have heq : raw9351step0 = -raw9351 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9351).symm
    injectiveMoment H raw9351step0 = injectiveMoment H raw9351step1 := by
      have heq : raw9351step1 = (fun i j => raw9351step0 (permutation313 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9351step0 permutation313 permutation15
    _ = injectiveMoment H node3120 := by rfl

theorem canonical9360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9360 = injectiveMoment H node3120 := by
  calc
    injectiveMoment H raw9360 = injectiveMoment H raw9360step0 := by
      have heq : raw9360step0 = -raw9360 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9360).symm
    injectiveMoment H raw9360step0 = injectiveMoment H raw9360step1 := by
      have heq : raw9360step1 = (fun i j => raw9360step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9360step0 permutation312 permutation15
    _ = injectiveMoment H node3120 := by rfl

theorem canonical9366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9366 = injectiveMoment H node2880 := by
  calc
    injectiveMoment H raw9366 = injectiveMoment H raw9366step0 := by
      have heq : raw9366step0 = -raw9366 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9366).symm
    injectiveMoment H raw9366step0 = injectiveMoment H raw9366step1 := by
      have heq : raw9366step1 = (fun i j => raw9366step0 (permutation404 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9366step0 permutation404 permutation23
    _ = injectiveMoment H node2880 := by rfl

theorem canonical9367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9367 = injectiveMoment H node2979 := by
  calc
    injectiveMoment H raw9367 = injectiveMoment H raw9367step0 := by
      have heq : raw9367step0 = -raw9367 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9367).symm
    injectiveMoment H raw9367step0 = injectiveMoment H raw9367step1 := by
      have heq : raw9367step1 = (fun i j => raw9367step0 (permutation395 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9367step0 permutation395 permutation17
    _ = injectiveMoment H node2979 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1088 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw1088 = injectiveMoment H raw1088step0 := by
      have heq : raw1088step0 = raw1088.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1088).symm
    injectiveMoment H raw1088step0 = injectiveMoment H raw1088step1 := by
      have heq : raw1088step1 = -raw1088step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1088step0).symm
    injectiveMoment H raw1088step1 = injectiveMoment H raw1088step2 := by
      have heq : raw1088step2 = (fun i j => raw1088step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1088step1 permutation16 permutation24
    _ = injectiveMoment H node1257 := by rfl

theorem canonical1094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1094 = injectiveMoment H node395 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1147 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw1147 = injectiveMoment H raw1147step0 := by
      have heq : raw1147step0 = -raw1147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1147).symm
    injectiveMoment H raw1147step0 = injectiveMoment H raw1147step1 := by
      have heq : raw1147step1 = (fun i j => raw1147step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1147step0 permutation19 permutation23
    _ = injectiveMoment H node1037 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1621 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw1621 = injectiveMoment H raw1621step0 := by
      have heq : raw1621step0 = (fun i j => raw1621 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1621 permutation10 permutation15
    _ = injectiveMoment H node775 := by rfl

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

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical4166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4166 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw4166 = injectiveMoment H raw4166step0 := by
      have heq : raw4166step0 = raw4166.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4166).symm
    injectiveMoment H raw4166step0 = injectiveMoment H raw4166step1 := by
      have heq : raw4166step1 = (fun i j => raw4166step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4166step0 permutation13 permutation3
    _ = injectiveMoment H node146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4925 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4925 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4925 = injectiveMoment H raw4925step0 := by
      have heq : raw4925step0 = -raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4925).symm
    injectiveMoment H raw4925step0 = injectiveMoment H raw4925step1 := by
      have heq : raw4925step1 = (fun i j => raw4925step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4925step0 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
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

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5615 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5615 = injectiveMoment H raw5615step0 := by
      have heq : raw5615step0 = raw5615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5615).symm
    injectiveMoment H raw5615step0 = injectiveMoment H raw5615step1 := by
      have heq : raw5615step1 = (fun i j => raw5615step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5615step0 permutation27 permutation6
    _ = injectiveMoment H node146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5639 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw5639 = injectiveMoment H raw5639step0 := by
      have heq : raw5639step0 = raw5639.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5639).symm
    injectiveMoment H raw5639step0 = injectiveMoment H raw5639step1 := by
      have heq : raw5639step1 = (fun i j => raw5639step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5639step0 permutation28 permutation8
    _ = injectiveMoment H node145 := by rfl

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

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7419 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7419 = injectiveMoment H raw7419step0 := by
      have heq : raw7419step0 = -raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7419).symm
    injectiveMoment H raw7419step0 = injectiveMoment H raw7419step1 := by
      have heq : raw7419step1 = (fun i j => raw7419step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7419step0 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

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

theorem canonical7985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7985 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw7985 = injectiveMoment H raw7985step0 := by
      have heq : raw7985step0 = (fun i j => raw7985 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7985 permutation5 permutation4
    _ = injectiveMoment H node59 := by rfl

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

theorem canonical8021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8021 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8021 = injectiveMoment H raw8021step0 := by
      have hz : ∀ i, raw8021 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8021step0 = (fun i j => raw8021 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8021 permutation9 hz
    _ = injectiveMoment H node31 := by rfl

theorem canonical8023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8023 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8023 = injectiveMoment H raw8023step0 := by
      have hz : ∀ i, raw8023 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8023step0 = (fun i j => raw8023 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8023 permutation9 hz
    _ = injectiveMoment H node32 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2121 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw2121 = injectiveMoment H raw2121step0 := by
      have heq : raw2121step0 = raw2121.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2121).symm
    injectiveMoment H raw2121step0 = injectiveMoment H raw2121step1 := by
      have heq : raw2121step1 = -raw2121step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2121step0).symm
    injectiveMoment H raw2121step1 = injectiveMoment H raw2121step2 := by
      have heq : raw2121step2 = (fun i j => raw2121step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2121step1 permutation10 permutation30
    _ = injectiveMoment H node1079 := by rfl

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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node146 = Sparse.eval value146 (momentVector H) := by
  have heq : pivotMatrix146 = (fun u v => node146 (pivotPermutation146 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node146 = injectiveMoment H pivotMatrix146 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix146 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix146 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix146 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix146 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (1 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix146 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix146 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node146 + (injectiveMoment H (mergeFirst pivotMatrix146 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix146 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix146 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value146, value31, value32, value36, Sparse.eval] at hc ⊢
  linarith

theorem sound151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node151 = Sparse.eval value151 (momentVector H) := by
  have hc : momentVector H 10 = injectiveMoment H node151 := rfl
  simp [value151, Sparse.eval, hc]

theorem sound153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node153 = Sparse.eval value153 (momentVector H) := by
  have heq : pivotMatrix153 = (fun u v => node153 (pivotPermutation153 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node153 = injectiveMoment H pivotMatrix153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix153 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix153 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node153 + (injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value153, value31, value35, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node155 = Sparse.eval value155 (momentVector H) := by
  have heq : pivotMatrix155 = (fun u v => node155 (pivotPermutation155 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node155 = injectiveMoment H pivotMatrix155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix155 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix155 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (0 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (1 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node155 + (injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value155, value32, value52, value53, Sparse.eval] at hc ⊢
  linarith

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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
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

theorem sound225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node225 = Sparse.eval value225 (momentVector H) := by
  have hc : momentVector H 228 = injectiveMoment H node225 := rfl
  simp [value225, Sparse.eval, hc]

theorem sound226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node226 = Sparse.eval value226 (momentVector H) := by
  have heq : pivotMatrix226 = (fun u v => node226 (pivotPermutation226 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node226 = injectiveMoment H pivotMatrix226 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix226 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix226 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (0 : Fin 3) = raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7419 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (1 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix226 (2 : Fin 3) = raw4925 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4925 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node226 + (injectiveMoment H (mergeFirst pivotMatrix226 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix226 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value226, value36, value43, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node228 = Sparse.eval value228 (momentVector H) := by
  have heq : pivotMatrix228 = (fun u v => node228 (pivotPermutation228 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node228 = injectiveMoment H pivotMatrix228 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix228 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix228 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (0 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (1 : Fin 3) = raw4963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4963 hH).trans (sound42 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix228 (2 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node228 + (injectiveMoment H (mergeFirst pivotMatrix228 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix228 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value228, value32, value42, value43, Sparse.eval] at hc ⊢
  linarith

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4209 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw4209 = injectiveMoment H raw4209step0 := by
      have heq : raw4209step0 = raw4209.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4209).symm
    injectiveMoment H raw4209step0 = injectiveMoment H raw4209step1 := by
      have heq : raw4209step1 = -raw4209step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4209step0).symm
    injectiveMoment H raw4209step1 = injectiveMoment H raw4209step2 := by
      have heq : raw4209step2 = (fun i j => raw4209step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4209step1 permutation26 permutation3
    _ = injectiveMoment H node146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical190
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6089 = injectiveMoment H node917 := by
  rfl

theorem canonical6093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6093 = injectiveMoment H node920 := by
  rfl

theorem canonical6094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6094 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw6094 = injectiveMoment H raw6094step0 := by
      have heq : raw6094step0 = raw6094.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6094).symm
    injectiveMoment H raw6094step0 = injectiveMoment H raw6094step1 := by
      have heq : raw6094step1 = (fun i j => raw6094step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6094step0 permutation31 permutation8
    _ = injectiveMoment H node248 := by rfl

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

theorem canonical6334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6334 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6334 = injectiveMoment H raw6334step0 := by
      have heq : raw6334step0 = raw6334.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6334).symm
    injectiveMoment H raw6334step0 = injectiveMoment H raw6334step1 := by
      have heq : raw6334step1 = (fun i j => raw6334step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6334step0 permutation28 permutation8
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6437 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6437 = injectiveMoment H raw6437step0 := by
      have heq : raw6437step0 = raw6437.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6437).symm
    injectiveMoment H raw6437step0 = injectiveMoment H raw6437step1 := by
      have heq : raw6437step1 = -raw6437step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6437step0).symm
    injectiveMoment H raw6437step1 = injectiveMoment H raw6437step2 := by
      have heq : raw6437step2 = (fun i j => raw6437step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6437step1 permutation27 permutation5
    _ = injectiveMoment H node145 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6532 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6532 = injectiveMoment H raw6532step0 := by
      have heq : raw6532step0 = raw6532.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6532).symm
    injectiveMoment H raw6532step0 = injectiveMoment H raw6532step1 := by
      have heq : raw6532step1 = -raw6532step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6532step0).symm
    injectiveMoment H raw6532step1 = injectiveMoment H raw6532step2 := by
      have heq : raw6532step2 = (fun i j => raw6532step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6532step1 permutation32 permutation3
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8069 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8069 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8069 = injectiveMoment H raw8069step0 := by
      have heq : raw8069step0 = -raw8069 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8069).symm
    injectiveMoment H raw8069step0 = injectiveMoment H raw8069step1 := by
      have hz : ∀ i, raw8069step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8069step1 = (fun i j => raw8069step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8069step0 permutation9 hz
    injectiveMoment H raw8069step1 = injectiveMoment H raw8069step2 := by
      have heq : raw8069step2 = (fun i j => raw8069step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8069step1 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8098 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8098 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8098 = injectiveMoment H raw8098step0 := by
      have heq : raw8098step0 = raw8098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8098).symm
    injectiveMoment H raw8098step0 = injectiveMoment H raw8098step1 := by
      have heq : raw8098step1 = -raw8098step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8098step0).symm
    injectiveMoment H raw8098step1 = injectiveMoment H raw8098step2 := by
      have hz : ∀ j, raw8098step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8098step2 = (fun i j => raw8098step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8098step1 permutation9 hz
    injectiveMoment H raw8098step2 = injectiveMoment H raw8098step3 := by
      have heq : raw8098step3 = (fun i j => raw8098step2 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8098step2 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

theorem canonical8099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8099 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8099 = injectiveMoment H raw8099step0 := by
      have heq : raw8099step0 = -raw8099 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8099).symm
    injectiveMoment H raw8099step0 = injectiveMoment H raw8099step1 := by
      have hz : ∀ i, raw8099step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8099step1 = (fun i j => raw8099step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8099step0 permutation9 hz
    injectiveMoment H raw8099step1 = injectiveMoment H raw8099step2 := by
      have heq : raw8099step2 = (fun i j => raw8099step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8099step1 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound775 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node775 = Sparse.eval value775 (momentVector H) := by
  have heq : pivotMatrix775 = (fun u v => node775 (pivotPermutation775 u) v) := by apply Matrix.ext; unfold pivotMatrix775 node775 pivotPermutation775; decide +kernel
  have hmoment : injectiveMoment H node775 = injectiveMoment H pivotMatrix775 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix775 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix775 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (0 : Fin 3) = raw8021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw8021; decide +kernel
    rw [heq]
    exact (canonical8021 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (1 : Fin 3) = raw5639 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5639; decide +kernel
    rw [heq]
    exact (canonical5639 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix775 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix775 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node775 + (injectiveMoment H (mergeFirst pivotMatrix775 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix775 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value775, value145, value146, value31, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6117 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw6117 = injectiveMoment H raw6117step0 := by
      have heq : raw6117step0 = raw6117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6117).symm
    injectiveMoment H raw6117step0 = injectiveMoment H raw6117step1 := by
      have heq : raw6117step1 = -raw6117step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6117step0).symm
    injectiveMoment H raw6117step1 = injectiveMoment H raw6117step2 := by
      have heq : raw6117step2 = (fun i j => raw6117step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6117step1 permutation15 permutation8
    _ = injectiveMoment H node228 := by rfl

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

theorem canonical6561 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6561 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw6561 = injectiveMoment H raw6561step0 := by
      have heq : raw6561step0 = raw6561.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6561).symm
    injectiveMoment H raw6561step0 = injectiveMoment H raw6561step1 := by
      have heq : raw6561step1 = -raw6561step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6561step0).symm
    injectiveMoment H raw6561step1 = injectiveMoment H raw6561step2 := by
      have heq : raw6561step2 = (fun i j => raw6561step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6561step1 permutation31 permutation3
    _ = injectiveMoment H node153 := by rfl

theorem canonical6565 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6565 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6565 = injectiveMoment H raw6565step0 := by
      have heq : raw6565step0 = raw6565.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6565).symm
    injectiveMoment H raw6565step0 = injectiveMoment H raw6565step1 := by
      have heq : raw6565step1 = -raw6565step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6565step0).symm
    injectiveMoment H raw6565step1 = injectiveMoment H raw6565step2 := by
      have heq : raw6565step2 = (fun i j => raw6565step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6565step1 permutation31 permutation3
    _ = injectiveMoment H node155 := by rfl

theorem canonical6566 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6566 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw6566 = injectiveMoment H raw6566step0 := by
      have heq : raw6566step0 = raw6566.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6566).symm
    injectiveMoment H raw6566step0 = injectiveMoment H raw6566step1 := by
      have heq : raw6566step1 = -raw6566step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6566step0).symm
    injectiveMoment H raw6566step1 = injectiveMoment H raw6566step2 := by
      have heq : raw6566step2 = (fun i j => raw6566step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6566step1 permutation31 permutation3
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical6224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6224 = injectiveMoment H node946 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7518 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw7518 = injectiveMoment H raw7518step0 := by
      have heq : raw7518step0 = raw7518.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7518).symm
    injectiveMoment H raw7518step0 = injectiveMoment H raw7518step1 := by
      have heq : raw7518step1 = -raw7518step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7518step0).symm
    injectiveMoment H raw7518step1 = injectiveMoment H raw7518step2 := by
      have heq : raw7518step2 = (fun i j => raw7518step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7518step1 permutation24 permutation3
    _ = injectiveMoment H node225 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7523 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7523 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw7523 = injectiveMoment H raw7523step0 := by
      have heq : raw7523step0 = raw7523.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7523).symm
    injectiveMoment H raw7523step0 = injectiveMoment H raw7523step1 := by
      have heq : raw7523step1 = -raw7523step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7523step0).symm
    injectiveMoment H raw7523step1 = injectiveMoment H raw7523step2 := by
      have heq : raw7523step2 = (fun i j => raw7523step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7523step1 permutation24 permutation3
    _ = injectiveMoment H node226 := by rfl

theorem canonical7533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7533 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7533 = injectiveMoment H raw7533step0 := by
      have heq : raw7533step0 = raw7533.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7533).symm
    injectiveMoment H raw7533step0 = injectiveMoment H raw7533step1 := by
      have heq : raw7533step1 = -raw7533step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7533step0).symm
    injectiveMoment H raw7533step1 = injectiveMoment H raw7533step2 := by
      have heq : raw7533step2 = (fun i j => raw7533step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7533step1 permutation24 permutation3
    _ = injectiveMoment H node153 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7911 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw7911 = injectiveMoment H raw7911step0 := by
      have heq : raw7911step0 = raw7911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7911).symm
    injectiveMoment H raw7911step0 = injectiveMoment H raw7911step1 := by
      have heq : raw7911step1 = -raw7911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7911step0).symm
    injectiveMoment H raw7911step1 = injectiveMoment H raw7911step2 := by
      have heq : raw7911step2 = (fun i j => raw7911step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7911step1 permutation24 permutation3
    _ = injectiveMoment H node247 := by rfl

theorem canonical7914 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7914 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7914 = injectiveMoment H raw7914step0 := by
      have heq : raw7914step0 = raw7914.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7914).symm
    injectiveMoment H raw7914step0 = injectiveMoment H raw7914step1 := by
      have heq : raw7914step1 = -raw7914step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7914step0).symm
    injectiveMoment H raw7914step1 = injectiveMoment H raw7914step2 := by
      have heq : raw7914step2 = (fun i j => raw7914step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7914step1 permutation24 permutation3
    _ = injectiveMoment H node261 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical8295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8295 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8295 = injectiveMoment H raw8295step0 := by
      have hz : ∀ i, raw8295 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8295step0 = (fun i j => raw8295 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8295 permutation9 hz
    injectiveMoment H raw8295step0 = injectiveMoment H raw8295step1 := by
      have heq : raw8295step1 = (fun i j => raw8295step0 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8295step0 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

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

theorem sound917 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node917 = Sparse.eval value917 (momentVector H) := by
  have heq : pivotMatrix917 = (fun u v => node917.transpose (pivotPermutation917 u) v) := by apply Matrix.ext; unfold pivotMatrix917 node917 pivotPermutation917; decide +kernel
  have hmoment : injectiveMoment H node917 = injectiveMoment H pivotMatrix917 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix917 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix917 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix917 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (0 : Fin 3) = raw4166 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw4166; decide +kernel
    rw [heq]
    exact (canonical4166 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix917 (1 : Fin 3)) =
      Sparse.eval value225 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (1 : Fin 3) = raw7518 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw7518; decide +kernel
    rw [heq]
    exact (canonical7518 hH).trans (sound225 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix917 (2 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix917 (2 : Fin 3) = raw7523 := by apply Matrix.ext; unfold mergeFirst pivotMatrix917 raw7523; decide +kernel
    rw [heq]
    exact (canonical7523 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node917 + (injectiveMoment H (mergeFirst pivotMatrix917 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix917 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix917 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value917, value146, value225, value226, Sparse.eval] at hc ⊢
  linarith

theorem sound920 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node920 = Sparse.eval value920 (momentVector H) := by
  have heq : pivotMatrix920 = (fun u v => node920 (pivotPermutation920 u) v) := by apply Matrix.ext; unfold pivotMatrix920 node920 pivotPermutation920; decide +kernel
  have hmoment : injectiveMoment H node920 = injectiveMoment H pivotMatrix920 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix920 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix920 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix920 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (0 : Fin 3) = raw8023 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw8023; decide +kernel
    rw [heq]
    exact (canonical8023 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix920 (1 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (1 : Fin 3) = raw6117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw6117; decide +kernel
    rw [heq]
    exact (canonical6117 hH).trans (sound228 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix920 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix920 (2 : Fin 3) = raw6094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix920 raw6094; decide +kernel
    rw [heq]
    exact (canonical6094 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node920 + (injectiveMoment H (mergeFirst pivotMatrix920 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix920 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix920 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value920, value228, value248, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound946 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node946 = Sparse.eval value946 (momentVector H) := by
  have heq : pivotMatrix946 = (fun u v => node946 (pivotPermutation946 u) v) := by apply Matrix.ext; unfold pivotMatrix946 node946 pivotPermutation946; decide +kernel
  have hmoment : injectiveMoment H node946 = injectiveMoment H pivotMatrix946 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix946 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix946 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix946 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (0 : Fin 3) = raw8295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw8295; decide +kernel
    rw [heq]
    exact (canonical8295 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix946 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (1 : Fin 3) = raw6334 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw6334; decide +kernel
    rw [heq]
    exact (canonical6334 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix946 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix946 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix946 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node946 + (injectiveMoment H (mergeFirst pivotMatrix946 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix946 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix946 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value946, value176, value229, value36, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6525 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6525 = injectiveMoment H raw6525step0 := by
      have heq : raw6525step0 = raw6525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6525).symm
    injectiveMoment H raw6525step0 = injectiveMoment H raw6525step1 := by
      have heq : raw6525step1 = -raw6525step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6525step0).symm
    injectiveMoment H raw6525step1 = injectiveMoment H raw6525step2 := by
      have heq : raw6525step2 = (fun i j => raw6525step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6525step1 permutation32 permutation3
    _ = injectiveMoment H node155 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7556 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7556 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw7556 = injectiveMoment H raw7556step0 := by
      have heq : raw7556step0 = raw7556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7556).symm
    injectiveMoment H raw7556step0 = injectiveMoment H raw7556step1 := by
      have heq : raw7556step1 = -raw7556step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7556step0).symm
    injectiveMoment H raw7556step1 = injectiveMoment H raw7556step2 := by
      have heq : raw7556step2 = (fun i j => raw7556step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7556step1 permutation22 permutation5
    _ = injectiveMoment H node145 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7602 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7602 = injectiveMoment H raw7602step0 := by
      have heq : raw7602step0 = raw7602.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7602).symm
    injectiveMoment H raw7602step0 = injectiveMoment H raw7602step1 := by
      have heq : raw7602step1 = -raw7602step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7602step0).symm
    injectiveMoment H raw7602step1 = injectiveMoment H raw7602step2 := by
      have heq : raw7602step2 = (fun i j => raw7602step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7602step1 permutation23 permutation3
    _ = injectiveMoment H node153 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1037 = Sparse.eval value1037 (momentVector H) := by
  have heq : pivotMatrix1037 = (fun u v => node1037 (pivotPermutation1037 u) v) := by apply Matrix.ext; unfold pivotMatrix1037 node1037 pivotPermutation1037; decide +kernel
  have hmoment : injectiveMoment H node1037 = injectiveMoment H pivotMatrix1037 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1037 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1037 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1037 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (0 : Fin 3) = raw8069 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw8069; decide +kernel
    rw [heq]
    exact (canonical8069 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1037 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (1 : Fin 3) = raw6561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw6561; decide +kernel
    rw [heq]
    exact (canonical6561 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1037 (2 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1037 (2 : Fin 3) = raw6437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1037 raw6437; decide +kernel
    rw [heq]
    exact (canonical6437 hH).trans (sound145 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1037 + (injectiveMoment H (mergeFirst pivotMatrix1037 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1037 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1037 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1037, value145, value153, value31, Sparse.eval] at hc ⊢
  linarith

theorem sound1075 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1075 = Sparse.eval value1075 (momentVector H) := by
  have heq : pivotMatrix1075 = (fun u v => node1075 (pivotPermutation1075 u) v) := by apply Matrix.ext; unfold pivotMatrix1075 node1075 pivotPermutation1075; decide +kernel
  have hmoment : injectiveMoment H node1075 = injectiveMoment H pivotMatrix1075 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1075 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1075 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1075 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (0 : Fin 3) = raw8098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw8098; decide +kernel
    rw [heq]
    exact (canonical8098 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1075 (1 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (1 : Fin 3) = raw6565 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw6565; decide +kernel
    rw [heq]
    exact (canonical6565 hH).trans (sound155 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1075 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1075 (2 : Fin 3) = raw6525 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1075 raw6525; decide +kernel
    rw [heq]
    exact (canonical6525 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1075 + (injectiveMoment H (mergeFirst pivotMatrix1075 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1075 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1075 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1075, value155, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound1079 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1079 = Sparse.eval value1079 (momentVector H) := by
  have heq : pivotMatrix1079 = (fun u v => node1079 (pivotPermutation1079 u) v) := by apply Matrix.ext; unfold pivotMatrix1079 node1079 pivotPermutation1079; decide +kernel
  have hmoment : injectiveMoment H node1079 = injectiveMoment H pivotMatrix1079 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1079 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1079 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (0 : Fin 3) = raw8099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw8099; decide +kernel
    rw [heq]
    exact (canonical8099 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (1 : Fin 3) = raw6566 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6566; decide +kernel
    rw [heq]
    exact (canonical6566 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1079 (2 : Fin 3) = raw6532 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1079 raw6532; decide +kernel
    rw [heq]
    exact (canonical6532 hH).trans (sound185 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1079 + (injectiveMoment H (mergeFirst pivotMatrix1079 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1079 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1079, value185, value36, Sparse.eval] at hc ⊢
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

theorem sound1113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1113 = Sparse.eval value1113 (momentVector H) := by
  have heq : pivotMatrix1113 = (fun u v => node1113.transpose (pivotPermutation1113 u) v) := by apply Matrix.ext; unfold pivotMatrix1113 node1113 pivotPermutation1113; decide +kernel
  have hmoment : injectiveMoment H node1113 = injectiveMoment H pivotMatrix1113 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1113 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1113 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1113 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (0 : Fin 3) = raw4209 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw4209; decide +kernel
    rw [heq]
    exact (canonical4209 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1113 (1 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (1 : Fin 3) = raw7556 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw7556; decide +kernel
    rw [heq]
    exact (canonical7556 hH).trans (sound145 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1113 (2 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1113 (2 : Fin 3) = raw7602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1113 raw7602; decide +kernel
    rw [heq]
    exact (canonical7602 hH).trans (sound153 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1113 + (injectiveMoment H (mergeFirst pivotMatrix1113 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1113 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1113 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1113, value145, value146, value153, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9964 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9964 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw9964 = injectiveMoment H raw9964step0 := by
      have heq : raw9964step0 = raw9964.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9964).symm
    injectiveMoment H raw9964step0 = injectiveMoment H raw9964step1 := by
      have heq : raw9964step1 = -raw9964step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9964step0).symm
    injectiveMoment H raw9964step1 = injectiveMoment H raw9964step2 := by
      have heq : raw9964step2 = (fun i j => raw9964step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9964step1 permutation21 permutation3
    _ = injectiveMoment H node151 := by rfl

theorem canonical9976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9976 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw9976 = injectiveMoment H raw9976step0 := by
      have heq : raw9976step0 = raw9976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9976).symm
    injectiveMoment H raw9976step0 = injectiveMoment H raw9976step1 := by
      have heq : raw9976step1 = -raw9976step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9976step0).symm
    injectiveMoment H raw9976step1 = injectiveMoment H raw9976step2 := by
      have heq : raw9976step2 = (fun i j => raw9976step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9976step1 permutation21 permutation3
    _ = injectiveMoment H node146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10096 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw10096 = injectiveMoment H raw10096step0 := by
      have heq : raw10096step0 = raw10096.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10096).symm
    injectiveMoment H raw10096step0 = injectiveMoment H raw10096step1 := by
      have heq : raw10096step1 = (fun i j => raw10096step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10096step0 permutation28 permutation4
    _ = injectiveMoment H node211 := by rfl

theorem canonical10098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10098 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw10098 = injectiveMoment H raw10098step0 := by
      have heq : raw10098step0 = raw10098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10098).symm
    injectiveMoment H raw10098step0 = injectiveMoment H raw10098step1 := by
      have heq : raw10098step1 = (fun i j => raw10098step0 (permutation28 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10098step0 permutation28 permutation4
    _ = injectiveMoment H node212 := by rfl

theorem canonical10102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10102 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw10102 = injectiveMoment H raw10102step0 := by
      have heq : raw10102step0 = raw10102.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10102).symm
    injectiveMoment H raw10102step0 = injectiveMoment H raw10102step1 := by
      have heq : raw10102step1 = (fun i j => raw10102step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10102step0 permutation27 permutation3
    _ = injectiveMoment H node228 := by rfl

theorem canonical10104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10104 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw10104 = injectiveMoment H raw10104step0 := by
      have heq : raw10104step0 = raw10104.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10104).symm
    injectiveMoment H raw10104step0 = injectiveMoment H raw10104step1 := by
      have heq : raw10104step1 = (fun i j => raw10104step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10104step0 permutation27 permutation3
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1257 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1257 = Sparse.eval value1257 (momentVector H) := by
  have heq : pivotMatrix1257 = (fun u v => node1257.transpose (pivotPermutation1257 u) v) := by apply Matrix.ext; unfold pivotMatrix1257 node1257 pivotPermutation1257; decide +kernel
  have hmoment : injectiveMoment H node1257 = injectiveMoment H pivotMatrix1257 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1257 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1257 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (0 : Fin 3) = raw7533 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw7533; decide +kernel
    rw [heq]
    exact (canonical7533 hH).trans (sound153 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) =
      Sparse.eval value151 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (1 : Fin 3) = raw9964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9964; decide +kernel
    rw [heq]
    exact (canonical9964 hH).trans (sound151 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1257 (2 : Fin 3) = raw9976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1257 raw9976; decide +kernel
    rw [heq]
    exact (canonical9976 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1257 + (injectiveMoment H (mergeFirst pivotMatrix1257 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1257 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1257, value146, value151, value153, Sparse.eval] at hc ⊢
  linarith

theorem sound1275 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1275 = Sparse.eval value1275 (momentVector H) := by
  have heq : pivotMatrix1275 = (fun u v => node1275.transpose (pivotPermutation1275 u) v) := by apply Matrix.ext; unfold pivotMatrix1275 node1275 pivotPermutation1275; decide +kernel
  have hmoment : injectiveMoment H node1275 = injectiveMoment H pivotMatrix1275 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1275 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1275 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1275 (0 : Fin 3)) =
      Sparse.eval value247 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (0 : Fin 3) = raw7911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw7911; decide +kernel
    rw [heq]
    exact (canonical7911 hH).trans (sound247 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1275 (1 : Fin 3)) =
      Sparse.eval value211 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (1 : Fin 3) = raw10096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw10096; decide +kernel
    rw [heq]
    exact (canonical10096 hH).trans (sound211 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1275 (2 : Fin 3)) =
      Sparse.eval value228 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1275 (2 : Fin 3) = raw10102 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1275 raw10102; decide +kernel
    rw [heq]
    exact (canonical10102 hH).trans (sound228 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1275 + (injectiveMoment H (mergeFirst pivotMatrix1275 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1275 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1275 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1275, value211, value228, value247, Sparse.eval] at hc ⊢
  linarith

theorem sound1277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1277 = Sparse.eval value1277 (momentVector H) := by
  have heq : pivotMatrix1277 = (fun u v => node1277.transpose (pivotPermutation1277 u) v) := by apply Matrix.ext; unfold pivotMatrix1277 node1277 pivotPermutation1277; decide +kernel
  have hmoment : injectiveMoment H node1277 = injectiveMoment H pivotMatrix1277 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1277 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1277 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (0 : Fin 3) = raw7914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw7914; decide +kernel
    rw [heq]
    exact (canonical7914 hH).trans (sound261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (1 : Fin 3) = raw10098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10098; decide +kernel
    rw [heq]
    exact (canonical10098 hH).trans (sound212 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1277 (2 : Fin 3) = raw10104 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1277 raw10104; decide +kernel
    rw [heq]
    exact (canonical10104 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1277 + (injectiveMoment H (mergeFirst pivotMatrix1277 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1277 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1277, value212, value229, value261, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node395 = Sparse.eval value395 (momentVector H) := by
  have hc : momentVector H 72 = injectiveMoment H node395 := rfl
  simp [value395, Sparse.eval, hc]

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

theorem sound459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node459 = Sparse.eval value459 (momentVector H) := by
  have hc : momentVector H 321 = injectiveMoment H node459 := rfl
  simp [value459, Sparse.eval, hc]

theorem sound474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node474 = Sparse.eval value474 (momentVector H) := by
  have hc : momentVector H 38 = injectiveMoment H node474 := rfl
  simp [value474, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound23
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1475 = Sparse.eval value1475 (momentVector H) := by
  have heq : pivotMatrix1475 = (fun u v => node1475 (pivotPermutation1475 u) v) := by apply Matrix.ext; unfold pivotMatrix1475 node1475 pivotPermutation1475; decide +kernel
  have hmoment : injectiveMoment H node1475 = injectiveMoment H pivotMatrix1475 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1475 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1475 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1475 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (0 : Fin 4) = raw1621 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1621; decide +kernel
    rw [heq]
    exact (canonical1621 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1475 (1 : Fin 4)) =
      Sparse.eval value1037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (1 : Fin 4) = raw1147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1147; decide +kernel
    rw [heq]
    exact (canonical1147 hH).trans (sound1037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1475 (2 : Fin 4)) =
      Sparse.eval value395 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (2 : Fin 4) = raw1094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1094; decide +kernel
    rw [heq]
    exact (canonical1094 hH).trans (sound395 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1475 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1475 (3 : Fin 4) = raw1088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1475 raw1088; decide +kernel
    rw [heq]
    exact (canonical1088 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1475 + (injectiveMoment H (mergeFirst pivotMatrix1475 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1475 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1475, value1037, value1257, value395, value775, Sparse.eval] at hc ⊢
  linarith

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

theorem sound582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node582 = Sparse.eval value582 (momentVector H) := by
  have hc : momentVector H 505 = injectiveMoment H node582 := rfl
  simp [value582, Sparse.eval, hc]

theorem sound585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node585 = Sparse.eval value585 (momentVector H) := by
  have hc : momentVector H 508 = injectiveMoment H node585 := rfl
  simp [value585, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1791 = injectiveMoment H node474 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1799 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1799 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw1799 = injectiveMoment H raw1799step0 := by
      have heq : raw1799step0 = raw1799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1799).symm
    injectiveMoment H raw1799step0 = injectiveMoment H raw1799step1 := by
      have heq : raw1799step1 = -raw1799step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1799step0).symm
    injectiveMoment H raw1799step1 = injectiveMoment H raw1799step2 := by
      have heq : raw1799step2 = (fun i j => raw1799step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1799step1 permutation10 permutation30
    _ = injectiveMoment H node1277 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2981 = injectiveMoment H node1932 := by
  rfl

theorem canonical2982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2982 = injectiveMoment H node1932 := by
  calc
    injectiveMoment H raw2982 = injectiveMoment H raw2982step0 := by
      have heq : raw2982step0 = (fun i j => raw2982 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2982 permutation34 permutation9
    _ = injectiveMoment H node1932 := by rfl

theorem canonical2983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2983 = injectiveMoment H node459 := by
  calc
    injectiveMoment H raw2983 = injectiveMoment H raw2983step0 := by
      have heq : raw2983step0 = raw2983.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2983).symm
    injectiveMoment H raw2983step0 = injectiveMoment H raw2983step1 := by
      have heq : raw2983step1 = (fun i j => raw2983step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2983step0 permutation27 permutation18
    _ = injectiveMoment H node459 := by rfl

theorem canonical2984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2984 = injectiveMoment H node1475 := by
  calc
    injectiveMoment H raw2984 = injectiveMoment H raw2984step0 := by
      have heq : raw2984step0 = (fun i j => raw2984 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2984 permutation42 permutation21
    _ = injectiveMoment H node1475 := by rfl

theorem canonical2987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2987 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw2987 = injectiveMoment H raw2987step0 := by
      have heq : raw2987step0 = -raw2987 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2987).symm
    injectiveMoment H raw2987step0 = injectiveMoment H raw2987step1 := by
      have heq : raw2987step1 = (fun i j => raw2987step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2987step0 permutation23 permutation15
    _ = injectiveMoment H node1113 := by rfl

theorem canonical2988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2988 = injectiveMoment H node1933 := by
  rfl

theorem canonical2989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2989 = injectiveMoment H node582 := by
  rfl

theorem canonical2991 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2991 = injectiveMoment H node1075 := by
  calc
    injectiveMoment H raw2991 = injectiveMoment H raw2991step0 := by
      have heq : raw2991step0 = raw2991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2991).symm
    injectiveMoment H raw2991step0 = injectiveMoment H raw2991step1 := by
      have heq : raw2991step1 = -raw2991step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2991step0).symm
    injectiveMoment H raw2991step1 = injectiveMoment H raw2991step2 := by
      have heq : raw2991step2 = (fun i j => raw2991step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2991step1 permutation12 permutation32
    _ = injectiveMoment H node1075 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3053 = injectiveMoment H node585 := by
  calc
    injectiveMoment H raw3053 = injectiveMoment H raw3053step0 := by
      have heq : raw3053step0 = (fun i j => raw3053 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3053 permutation12 permutation9
    _ = injectiveMoment H node585 := by rfl

theorem canonical3054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3054 = injectiveMoment H node1275 := by
  calc
    injectiveMoment H raw3054 = injectiveMoment H raw3054step0 := by
      have heq : raw3054step0 = raw3054.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3054).symm
    injectiveMoment H raw3054step0 = injectiveMoment H raw3054step1 := by
      have heq : raw3054step1 = -raw3054step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3054step0).symm
    injectiveMoment H raw3054step1 = injectiveMoment H raw3054step2 := by
      have heq : raw3054step2 = (fun i j => raw3054step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3054step1 permutation12 permutation32
    _ = injectiveMoment H node1275 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3152 = injectiveMoment H node1657 := by
  calc
    injectiveMoment H raw3152 = injectiveMoment H raw3152step0 := by
      have heq : raw3152step0 = (fun i j => raw3152 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3152 permutation39 permutation11
    _ = injectiveMoment H node1657 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1657 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1657 = Sparse.eval value1657 (momentVector H) := by
  have heq : pivotMatrix1657 = (fun u v => node1657 (pivotPermutation1657 u) v) := by apply Matrix.ext; unfold pivotMatrix1657 node1657 pivotPermutation1657; decide +kernel
  have hmoment : injectiveMoment H node1657 = injectiveMoment H pivotMatrix1657 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1657 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1657 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1657 (0 : Fin 4)) =
      Sparse.eval value946 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (0 : Fin 4) = raw6224 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw6224; decide +kernel
    rw [heq]
    exact (canonical6224 hH).trans (sound946 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1657 (1 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (1 : Fin 4) = raw2121 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw2121; decide +kernel
    rw [heq]
    exact (canonical2121 hH).trans (sound1079 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1657 (2 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (2 : Fin 4) = raw1799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw1799; decide +kernel
    rw [heq]
    exact (canonical1799 hH).trans (sound1277 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1657 (3 : Fin 4)) =
      Sparse.eval value474 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1657 (3 : Fin 4) = raw1791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1657 raw1791; decide +kernel
    rw [heq]
    exact (canonical1791 hH).trans (sound474 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1657 + (injectiveMoment H (mergeFirst pivotMatrix1657 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1657 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1657, value1079, value1277, value474, value946, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1932 = Sparse.eval value1932 (momentVector H) := by
  have heq : pivotMatrix1932 = (fun u v => node1932 (pivotPermutation1932 u) v) := by apply Matrix.ext; unfold pivotMatrix1932 node1932 pivotPermutation1932; decide +kernel
  have hmoment : injectiveMoment H node1932 = injectiveMoment H pivotMatrix1932 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1932 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1932 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1932 (0 : Fin 4)) =
      Sparse.eval value917 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (0 : Fin 4) = raw6089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw6089; decide +kernel
    rw [heq]
    exact (canonical6089 hH).trans (sound917 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1932 (1 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (1 : Fin 4) = raw3053 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw3053; decide +kernel
    rw [heq]
    exact (canonical3053 hH).trans (sound585 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1932 (2 : Fin 4)) =
      Sparse.eval value1113 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (2 : Fin 4) = raw2987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw2987; decide +kernel
    rw [heq]
    exact (canonical2987 hH).trans (sound1113 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1932 (3 : Fin 4)) =
      Sparse.eval value459 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1932 (3 : Fin 4) = raw2983 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1932 raw2983; decide +kernel
    rw [heq]
    exact (canonical2983 hH).trans (sound459 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1932 + (injectiveMoment H (mergeFirst pivotMatrix1932 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1932 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1932, value1113, value459, value585, value917, Sparse.eval] at hc ⊢
  linarith

theorem sound1933 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1933 = Sparse.eval value1933 (momentVector H) := by
  have heq : pivotMatrix1933 = (fun u v => node1933 (pivotPermutation1933 u) v) := by apply Matrix.ext; unfold pivotMatrix1933 node1933 pivotPermutation1933; decide +kernel
  have hmoment : injectiveMoment H node1933 = injectiveMoment H pivotMatrix1933 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1933 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1933 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1933 (0 : Fin 4)) =
      Sparse.eval value920 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (0 : Fin 4) = raw6093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw6093; decide +kernel
    rw [heq]
    exact (canonical6093 hH).trans (sound920 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1933 (1 : Fin 4)) =
      Sparse.eval value1275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (1 : Fin 4) = raw3054 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw3054; decide +kernel
    rw [heq]
    exact (canonical3054 hH).trans (sound1275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1933 (2 : Fin 4)) =
      Sparse.eval value1075 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (2 : Fin 4) = raw2991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw2991; decide +kernel
    rw [heq]
    exact (canonical2991 hH).trans (sound1075 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1933 (3 : Fin 4)) =
      Sparse.eval value582 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1933 (3 : Fin 4) = raw2989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1933 raw2989; decide +kernel
    rw [heq]
    exact (canonical2989 hH).trans (sound582 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1933 + (injectiveMoment H (mergeFirst pivotMatrix1933 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1933 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1933, value1075, value1275, value582, value920, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound48
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3121 = Sparse.eval value3121 (momentVector H) := by
  have heq : pivotMatrix3121 = (fun u v => node3121 (pivotPermutation3121 u) v) := by apply Matrix.ext; unfold pivotMatrix3121 node3121 pivotPermutation3121; decide +kernel
  have hmoment : injectiveMoment H node3121 = injectiveMoment H pivotMatrix3121 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3121 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3121 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3121 (0 : Fin 5)) =
      Sparse.eval value1657 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3121 (0 : Fin 5) = raw3152 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3121 raw3152; decide +kernel
    rw [heq]
    exact (canonical3152 hH).trans (sound1657 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3121 (1 : Fin 5)) =
      Sparse.eval value1933 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3121 (1 : Fin 5) = raw2988 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3121 raw2988; decide +kernel
    rw [heq]
    exact (canonical2988 hH).trans (sound1933 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3121 (2 : Fin 5)) =
      Sparse.eval value1475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3121 (2 : Fin 5) = raw2984 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3121 raw2984; decide +kernel
    rw [heq]
    exact (canonical2984 hH).trans (sound1475 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3121 (3 : Fin 5)) =
      Sparse.eval value1932 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3121 (3 : Fin 5) = raw2982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3121 raw2982; decide +kernel
    rw [heq]
    exact (canonical2982 hH).trans (sound1932 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3121 (4 : Fin 5)) =
      Sparse.eval value1932 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3121 (4 : Fin 5) = raw2981 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3121 raw2981; decide +kernel
    rw [heq]
    exact (canonical2981 hH).trans (sound1932 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3121 + (injectiveMoment H (mergeFirst pivotMatrix3121 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3121 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3121 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3121 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3121 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3121, value1475, value1657, value1932, value1933, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound338 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow338 (momentVector H) = 0 := by
  have hshape : boundaryMatrix338 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix338 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix338 (0 : Fin 6)) =
      Sparse.eval value3121 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (0 : Fin 6) = raw9106 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9106 hH).trans (sound3121 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix338 (1 : Fin 6)) =
      Sparse.eval value3121 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (1 : Fin 6) = raw9235 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9235 hH).trans (sound3121 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix338 (2 : Fin 6)) =
      Sparse.eval value3120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (2 : Fin 6) = raw9351 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9351 hH).trans (sound3120_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix338 (3 : Fin 6)) =
      Sparse.eval value3120 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (3 : Fin 6) = raw9360 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9360 hH).trans (sound3120_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix338 (4 : Fin 6)) =
      Sparse.eval value2880 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (4 : Fin 6) = raw9366 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9366 hH).trans (sound2880_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix338 (5 : Fin 6)) =
      Sparse.eval value2979 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix338 (5 : Fin 6) = raw9367 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9367 hH).trans (sound2979_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix338 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix338 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow338, value2880, value2979, value3120, value3121, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck183 : Integer.Sparse.reindex coordinateMap (PairData.rows 183) =
    PairSemantics.boundaryRow338 := by decide +kernel

theorem rowSound183_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 183) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck183]
  exact PairSemantics.boundarySound338 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e_oai
