-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:31:55.518783+00:00
-- url     : https://prove2.me/submissions/87215a43-7f20-43b0-aeb1-f619e8319479

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3317_e

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

theorem canonical9088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9088 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw9088 = injectiveMoment H raw9088step0 := by
      have heq : raw9088step0 = raw9088.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9088).symm
    injectiveMoment H raw9088step0 = injectiveMoment H raw9088step1 := by
      have heq : raw9088step1 = (fun i j => raw9088step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9088step0 permutation18 permutation7
    _ = injectiveMoment H node291 := by rfl

theorem canonical9094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9094 = injectiveMoment H node3318 := by
  calc
    injectiveMoment H raw9094 = injectiveMoment H raw9094step0 := by
      have heq : raw9094step0 = (fun i j => raw9094 (permutation364 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9094 permutation364 permutation16
    _ = injectiveMoment H node3318 := by rfl

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

theorem canonical9224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9224 = injectiveMoment H node3318 := by
  calc
    injectiveMoment H raw9224 = injectiveMoment H raw9224step0 := by
      have heq : raw9224step0 = (fun i j => raw9224 (permutation363 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9224 permutation363 permutation16
    _ = injectiveMoment H node3318 := by rfl

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

theorem canonical9279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9279 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw9279 = injectiveMoment H raw9279step0 := by
      have hz : ∀ j, raw9279 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw9279step0 = (fun i j => raw9279 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9279 permutation221 hz
    injectiveMoment H raw9279step0 = injectiveMoment H raw9279step1 := by
      have heq : raw9279step1 = (fun i j => raw9279step0 (permutation139 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9279step0 permutation139 permutation20
    _ = injectiveMoment H node1746 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9289 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw9289 = injectiveMoment H raw9289step0 := by
      have hz : ∀ j, raw9289 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9289step0 = (fun i j => raw9289 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9289 permutation241 hz
    injectiveMoment H raw9289step0 = injectiveMoment H raw9289step1 := by
      have heq : raw9289step1 = (fun i j => raw9289step0 (permutation139 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9289step0 permutation139 permutation20
    _ = injectiveMoment H node1746 := by rfl

theorem canonical9290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9290 = injectiveMoment H node3317 := by
  calc
    injectiveMoment H raw9290 = injectiveMoment H raw9290step0 := by
      have heq : raw9290step0 = (fun i j => raw9290 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9290 permutation258 permutation9
    _ = injectiveMoment H node3317 := by rfl

theorem canonical9291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9291 = injectiveMoment H node3165 := by
  calc
    injectiveMoment H raw9291 = injectiveMoment H raw9291step0 := by
      have heq : raw9291step0 = (fun i j => raw9291 (permutation258 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9291 permutation258 permutation12
    _ = injectiveMoment H node3165 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1309 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw1309 = injectiveMoment H raw1309step0 := by
      have heq : raw1309step0 = raw1309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1309).symm
    injectiveMoment H raw1309step0 = injectiveMoment H raw1309step1 := by
      have heq : raw1309step1 = (fun i j => raw1309step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1309step0 permutation25 permutation18
    _ = injectiveMoment H node1027 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2411 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw2411 = injectiveMoment H raw2411step0 := by
      have heq : raw2411step0 = raw2411.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2411).symm
    injectiveMoment H raw2411step0 = injectiveMoment H raw2411step1 := by
      have hz : ∀ i, raw2411step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw2411step1 = (fun i j => raw2411step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2411step0 permutation21 hz
    injectiveMoment H raw2411step1 = injectiveMoment H raw2411step2 := by
      have heq : raw2411step2 = (fun i j => raw2411step1 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2411step1 permutation25 permutation6
    _ = injectiveMoment H node291 := by rfl

theorem canonical2419 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2419 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw2419 = injectiveMoment H raw2419step0 := by
      have heq : raw2419step0 = raw2419.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2419).symm
    injectiveMoment H raw2419step0 = injectiveMoment H raw2419step1 := by
      have heq : raw2419step1 = (fun i j => raw2419step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2419step0 permutation22 permutation17
    _ = injectiveMoment H node1107 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw337 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw337 = injectiveMoment H raw337step0 := by
      have heq : raw337step0 = raw337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw337).symm
    injectiveMoment H raw337step0 = injectiveMoment H raw337step1 := by
      have heq : raw337step1 = (fun i j => raw337step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw337step0 permutation16 permutation5
    _ = injectiveMoment H node192 := by rfl

theorem canonical338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw338 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw338 = injectiveMoment H raw338step0 := by
      have heq : raw338step0 = raw338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw338).symm
    _ = injectiveMoment H node101 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3638 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw3638 = injectiveMoment H raw3638step0 := by
      have heq : raw3638step0 = raw3638.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3638).symm
    _ = injectiveMoment H node224 := by rfl

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

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

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

theorem canonical8216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8216 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8216 = injectiveMoment H raw8216step0 := by
      have hz : ∀ j, raw8216 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8216step0 = (fun i j => raw8216 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8216 permutation7 hz
    injectiveMoment H raw8216step0 = injectiveMoment H raw8216step1 := by
      have hz : ∀ i, raw8216step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8216step1 = (fun i j => raw8216step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8216step0 permutation3 hz
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

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node101 = Sparse.eval value101 (momentVector H) := by
  have hc : momentVector H 63 = injectiveMoment H node101 := rfl
  simp [value101, Sparse.eval, hc]

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

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

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

theorem sound192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node192 = Sparse.eval value192 (momentVector H) := by
  have hc : momentVector H 196 = injectiveMoment H node192 := rfl
  simp [value192, Sparse.eval, hc]

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

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

theorem canonical5850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5850 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw5850 = injectiveMoment H raw5850step0 := by
      have heq : raw5850step0 = raw5850.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5850).symm
    injectiveMoment H raw5850step0 = injectiveMoment H raw5850step1 := by
      have heq : raw5850step1 = (fun i j => raw5850step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5850step0 permutation30 permutation5
    _ = injectiveMoment H node224 := by rfl

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

theorem canonical8167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8167 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8167 = injectiveMoment H raw8167step0 := by
      have heq : raw8167step0 = (fun i j => raw8167 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8167 permutation5 permutation4
    _ = injectiveMoment H node62 := by rfl

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

theorem sound291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node291 = Sparse.eval value291 (momentVector H) := by
  have heq : pivotMatrix291 = (fun u v => node291 (pivotPermutation291 u) v) := by apply Matrix.ext; unfold pivotMatrix291 node291 pivotPermutation291; decide +kernel
  have hmoment : injectiveMoment H node291 = injectiveMoment H pivotMatrix291 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix291 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix291 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (1 : Fin 3) = raw8167 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8167; decide +kernel
    rw [heq]
    exact (canonical8167 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix291 (2 : Fin 3) = raw8216 := by apply Matrix.ext; unfold mergeFirst pivotMatrix291 raw8216; decide +kernel
    rw [heq]
    exact (canonical8216 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node291 + (injectiveMoment H (mergeFirst pivotMatrix291 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix291 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value291, value4, value57, value62, Sparse.eval] at hc ⊢
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

theorem sound719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node719 = Sparse.eval value719 (momentVector H) := by
  have hc : momentVector H 230 = injectiveMoment H node719 := rfl
  simp [value719, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3289 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw3289 = injectiveMoment H raw3289step0 := by
      have heq : raw3289step0 = raw3289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3289).symm
    _ = injectiveMoment H node162 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3329 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw3329 = injectiveMoment H raw3329step0 := by
      have heq : raw3329step0 = raw3329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3329).symm
    injectiveMoment H raw3329step0 = injectiveMoment H raw3329step1 := by
      have heq : raw3329step1 = (fun i j => raw3329step0 (permutation22 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3329step0 permutation22 permutation21
    _ = injectiveMoment H node1304 := by rfl

theorem canonical3338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3338 = injectiveMoment H node605 := by
  rfl

theorem canonical3349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3349 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3349 = injectiveMoment H raw3349step0 := by
      have heq : raw3349step0 = raw3349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3349).symm
    _ = injectiveMoment H node197 := by rfl

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

theorem sound789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node789 = Sparse.eval value789 (momentVector H) := by
  have heq : pivotMatrix789 = (fun u v => node789.transpose (pivotPermutation789 u) v) := by apply Matrix.ext; unfold pivotMatrix789 node789 pivotPermutation789; decide +kernel
  have hmoment : injectiveMoment H node789 = injectiveMoment H pivotMatrix789 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix789 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix789 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix789 (0 : Fin 3)) =
      Sparse.eval value192 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (0 : Fin 3) = raw337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw337; decide +kernel
    rw [heq]
    exact (canonical337 hH).trans (sound192 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix789 (1 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (1 : Fin 3) = raw3289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw3289; decide +kernel
    rw [heq]
    exact (canonical3289 hH).trans (sound162 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix789 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix789 (2 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix789 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node789 + (injectiveMoment H (mergeFirst pivotMatrix789 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix789 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix789 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value789, value162, value192, value197, Sparse.eval] at hc ⊢
  linarith

theorem sound825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node825 = Sparse.eval value825 (momentVector H) := by
  have heq : pivotMatrix825 = (fun u v => node825.transpose (pivotPermutation825 u) v) := by apply Matrix.ext; unfold pivotMatrix825 node825 pivotPermutation825; decide +kernel
  have hmoment : injectiveMoment H node825 = injectiveMoment H pivotMatrix825 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix825 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix825 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix825 (0 : Fin 3)) =
      Sparse.eval value101 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (0 : Fin 3) = raw338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw338; decide +kernel
    rw [heq]
    exact (canonical338 hH).trans (sound101 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix825 (1 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (1 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix825 (2 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix825 (2 : Fin 3) = raw3638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix825 raw3638; decide +kernel
    rw [heq]
    exact (canonical3638 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node825 + (injectiveMoment H (mergeFirst pivotMatrix825 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix825 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix825 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value825, value101, value197, value224, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7257 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw7257 = injectiveMoment H raw7257step0 := by
      have heq : raw7257step0 = raw7257.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7257).symm
    _ = injectiveMoment H node279 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8263 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw8263 = injectiveMoment H raw8263step0 := by
      have heq : raw8263step0 = raw8263.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8263).symm
    injectiveMoment H raw8263step0 = injectiveMoment H raw8263step1 := by
      have heq : raw8263step1 = (fun i j => raw8263step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8263step0 permutation30 permutation5
    _ = injectiveMoment H node291 := by rfl

theorem canonical8267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8267 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw8267 = injectiveMoment H raw8267step0 := by
      have heq : raw8267step0 = raw8267.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8267).symm
    injectiveMoment H raw8267step0 = injectiveMoment H raw8267step1 := by
      have heq : raw8267step1 = (fun i j => raw8267step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8267step0 permutation19 permutation3
    _ = injectiveMoment H node197 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7281 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7281 = injectiveMoment H raw7281step0 := by
      have heq : raw7281step0 = raw7281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7281).symm
    _ = injectiveMoment H node291 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7358 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7358 = injectiveMoment H raw7358step0 := by
      have heq : raw7358step0 = raw7358.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7358).symm
    injectiveMoment H raw7358step0 = injectiveMoment H raw7358step1 := by
      have heq : raw7358step1 = (fun i j => raw7358step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7358step0 permutation11 permutation4
    _ = injectiveMoment H node291 := by rfl

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

theorem canonical2191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2191 = injectiveMoment H node1746 := by
  rfl

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

theorem sound1027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1027 = Sparse.eval value1027 (momentVector H) := by
  have heq : pivotMatrix1027 = (fun u v => node1027.transpose (pivotPermutation1027 u) v) := by apply Matrix.ext; unfold pivotMatrix1027 node1027 pivotPermutation1027; decide +kernel
  have hmoment : injectiveMoment H node1027 = injectiveMoment H pivotMatrix1027 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1027 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1027 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (0 : Fin 3) = raw3349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw3349; decide +kernel
    rw [heq]
    exact (canonical3349 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (1 : Fin 3) = raw7257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7257; decide +kernel
    rw [heq]
    exact (canonical7257 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1027 (2 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1027 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1027 + (injectiveMoment H (mergeFirst pivotMatrix1027 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1027 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1027, value197, value279, value291, Sparse.eval] at hc ⊢
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

theorem sound1107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1107 = Sparse.eval value1107 (momentVector H) := by
  have heq : pivotMatrix1107 = (fun u v => node1107.transpose (pivotPermutation1107 u) v) := by apply Matrix.ext; unfold pivotMatrix1107 node1107 pivotPermutation1107; decide +kernel
  have hmoment : injectiveMoment H node1107 = injectiveMoment H pivotMatrix1107 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1107 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1107 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1107 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (0 : Fin 3) = raw3638 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw3638; decide +kernel
    rw [heq]
    exact (canonical3638 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1107 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (1 : Fin 3) = raw7281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw7281; decide +kernel
    rw [heq]
    exact (canonical7281 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1107 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1107 (2 : Fin 3) = raw7358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1107 raw7358; decide +kernel
    rw [heq]
    exact (canonical7358 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1107 + (injectiveMoment H (mergeFirst pivotMatrix1107 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1107 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1107 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1107, value224, value291, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7824 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7824 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7824 = injectiveMoment H raw7824step0 := by
      have heq : raw7824step0 = raw7824.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7824).symm
    injectiveMoment H raw7824step0 = injectiveMoment H raw7824step1 := by
      have heq : raw7824step1 = (fun i j => raw7824step0 (permutation20 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7824step0 permutation20 permutation8
    _ = injectiveMoment H node291 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1304 = Sparse.eval value1304 (momentVector H) := by
  have heq : pivotMatrix1304 = (fun u v => node1304.transpose (pivotPermutation1304 u) v) := by apply Matrix.ext; unfold pivotMatrix1304 node1304 pivotPermutation1304; decide +kernel
  have hmoment : injectiveMoment H node1304 = injectiveMoment H pivotMatrix1304 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1304 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1304 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1304 (0 : Fin 3)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (0 : Fin 3) = raw5850 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw5850; decide +kernel
    rw [heq]
    exact (canonical5850 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1304 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (1 : Fin 3) = raw8263 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw8263; decide +kernel
    rw [heq]
    exact (canonical8263 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1304 (2 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1304 (2 : Fin 3) = raw8267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1304 raw8267; decide +kernel
    rw [heq]
    exact (canonical8267 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1304 + (injectiveMoment H (mergeFirst pivotMatrix1304 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1304 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1304 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1304, value197, value224, value291, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3382 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3382 = injectiveMoment H raw3382step0 := by
      have hz : ∀ j, raw3382 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3382step0 = (fun i j => raw3382 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3382 permutation80 hz
    injectiveMoment H raw3382step0 = injectiveMoment H raw3382step1 := by
      have heq : raw3382step1 = (fun i j => raw3382step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3382step0 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

theorem canonical3388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3388 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3388 = injectiveMoment H raw3388step0 := by
      have hz : ∀ j, raw3388 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw3388step0 = (fun i j => raw3388 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3388 permutation104 hz
    injectiveMoment H raw3388step0 = injectiveMoment H raw3388step1 := by
      have heq : raw3388step1 = (fun i j => raw3388step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3388step0 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

theorem canonical3390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3390 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw3390 = injectiveMoment H raw3390step0 := by
      have heq : raw3390step0 = (fun i j => raw3390 (permutation136 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3390 permutation136 permutation30
    _ = injectiveMoment H node1746 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2293 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw2293 = injectiveMoment H raw2293step0 := by
      have heq : raw2293step0 = raw2293.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2293).symm
    injectiveMoment H raw2293step0 = injectiveMoment H raw2293step1 := by
      have hz : ∀ i, raw2293step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2293step1 = (fun i j => raw2293step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2293step0 permutation15 hz
    injectiveMoment H raw2293step1 = injectiveMoment H raw2293step2 := by
      have heq : raw2293step2 = (fun i j => raw2293step1 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2293step1 permutation25 permutation6
    _ = injectiveMoment H node291 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1746 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1746 = Sparse.eval value1746 (momentVector H) := by
  have heq : pivotMatrix1746 = (fun u v => node1746 (pivotPermutation1746 u) v) := by apply Matrix.ext; unfold pivotMatrix1746 node1746 pivotPermutation1746; decide +kernel
  have hmoment : injectiveMoment H node1746 = injectiveMoment H pivotMatrix1746 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1746 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1746 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1746 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (0 : Fin 4) = raw1309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw1309; decide +kernel
    rw [heq]
    exact (canonical1309 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1746 (1 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (1 : Fin 4) = raw2293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2293; decide +kernel
    rw [heq]
    exact (canonical2293 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1746 (2 : Fin 4)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (2 : Fin 4) = raw2411 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2411; decide +kernel
    rw [heq]
    exact (canonical2411 hH).trans (sound291 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1746 (3 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1746 (3 : Fin 4) = raw2419 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1746 raw2419; decide +kernel
    rw [heq]
    exact (canonical2419 hH).trans (sound1107 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1746 + (injectiveMoment H (mergeFirst pivotMatrix1746 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1746 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1746, value1027, value1107, value291, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9148 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9148 = injectiveMoment H raw9148step0 := by
      have hz : ∀ j, raw9148 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw9148step0 = (fun i j => raw9148 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9148 permutation7 hz
    injectiveMoment H raw9148step0 = injectiveMoment H raw9148step1 := by
      have hz : ∀ i, raw9148step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw9148step1 = (fun i j => raw9148step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9148step0 permutation15 hz
    injectiveMoment H raw9148step1 = injectiveMoment H raw9148step2 := by
      have hz : ∀ i, raw9148step1 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9148step2 = (fun i j => raw9148step1 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9148step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem sound587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node587 = Sparse.eval value587 (momentVector H) := by
  have hc : momentVector H 129 = injectiveMoment H node587 := rfl
  simp [value587, Sparse.eval, hc]

theorem sound605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node605 = Sparse.eval value605 (momentVector H) := by
  have hc : momentVector H 14 = injectiveMoment H node605 := rfl
  simp [value605, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1357 = Sparse.eval value1357 (momentVector H) := by
  have heq : pivotMatrix1357 = (fun u v => node1357 (pivotPermutation1357 u) v) := by apply Matrix.ext; unfold pivotMatrix1357 node1357 pivotPermutation1357; decide +kernel
  have hmoment : injectiveMoment H node1357 = injectiveMoment H pivotMatrix1357 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1357 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1357 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1357 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (0 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1357 (1 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (1 : Fin 3) = raw9088 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw9088; decide +kernel
    rw [heq]
    exact (canonical9088 hH).trans (sound291 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1357 (2 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1357 (2 : Fin 3) = raw9148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1357 raw9148; decide +kernel
    rw [heq]
    exact (canonical9148 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1357 + (injectiveMoment H (mergeFirst pivotMatrix1357 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1357 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1357 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1357, value291, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5281 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw5281 = injectiveMoment H raw5281step0 := by
      have heq : raw5281step0 = raw5281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5281).symm
    injectiveMoment H raw5281step0 = injectiveMoment H raw5281step1 := by
      have hz : ∀ i, raw5281step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5281step1 = (fun i j => raw5281step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5281step0 permutation15 hz
    injectiveMoment H raw5281step1 = injectiveMoment H raw5281step2 := by
      have heq : raw5281step2 = (fun i j => raw5281step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5281step1 permutation29 permutation6
    _ = injectiveMoment H node197 := by rfl

theorem canonical5289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5289 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw5289 = injectiveMoment H raw5289step0 := by
      have heq : raw5289step0 = raw5289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5289).symm
    injectiveMoment H raw5289step0 = injectiveMoment H raw5289step1 := by
      have heq : raw5289step1 = (fun i j => raw5289step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5289step0 permutation29 permutation18
    _ = injectiveMoment H node1027 := by rfl

theorem canonical5292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5292 = injectiveMoment H node825 := by
  calc
    injectiveMoment H raw5292 = injectiveMoment H raw5292step0 := by
      have heq : raw5292step0 = raw5292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5292).symm
    injectiveMoment H raw5292step0 = injectiveMoment H raw5292step1 := by
      have heq : raw5292step1 = (fun i j => raw5292step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5292step0 permutation29 permutation18
    _ = injectiveMoment H node825 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5317 = injectiveMoment H node2352 := by
  rfl

theorem canonical5323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5323 = injectiveMoment H node719 := by
  rfl

theorem canonical5325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5325 = injectiveMoment H node587 := by
  calc
    injectiveMoment H raw5325 = injectiveMoment H raw5325step0 := by
      have heq : raw5325step0 = raw5325.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5325).symm
    injectiveMoment H raw5325step0 = injectiveMoment H raw5325step1 := by
      have heq : raw5325step1 = (fun i j => raw5325step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5325step0 permutation23 permutation19
    _ = injectiveMoment H node587 := by rfl

theorem canonical5338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5338 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5338 = injectiveMoment H raw5338step0 := by
      have heq : raw5338step0 = raw5338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5338).symm
    injectiveMoment H raw5338step0 = injectiveMoment H raw5338step1 := by
      have hz : ∀ i, raw5338step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw5338step1 = (fun i j => raw5338step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5338step0 permutation80 hz
    injectiveMoment H raw5338step1 = injectiveMoment H raw5338step2 := by
      have heq : raw5338step2 = (fun i j => raw5338step1 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5338step1 permutation23 permutation20
    _ = injectiveMoment H node1304 := by rfl

theorem canonical5341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5341 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw5341 = injectiveMoment H raw5341step0 := by
      have heq : raw5341step0 = (fun i j => raw5341 (permutation33 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5341 permutation33 permutation12
    _ = injectiveMoment H node1746 := by rfl

theorem canonical5342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5342 = injectiveMoment H node2358 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5347 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw5347 = injectiveMoment H raw5347step0 := by
      have heq : raw5347step0 = raw5347.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5347).symm
    injectiveMoment H raw5347step0 = injectiveMoment H raw5347step1 := by
      have heq : raw5347step1 = (fun i j => raw5347step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5347step0 permutation23 permutation20
    _ = injectiveMoment H node1304 := by rfl

theorem canonical5355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5355 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw5355 = injectiveMoment H raw5355step0 := by
      have heq : raw5355step0 = raw5355.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5355).symm
    injectiveMoment H raw5355step0 = injectiveMoment H raw5355step1 := by
      have hz : ∀ i, raw5355step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5355step1 = (fun i j => raw5355step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5355step0 permutation15 hz
    injectiveMoment H raw5355step1 = injectiveMoment H raw5355step2 := by
      have heq : raw5355step2 = (fun i j => raw5355step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5355step1 permutation27 permutation5
    _ = injectiveMoment H node224 := by rfl

theorem canonical5363 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5363 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw5363 = injectiveMoment H raw5363step0 := by
      have heq : raw5363step0 = raw5363.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5363).symm
    injectiveMoment H raw5363step0 = injectiveMoment H raw5363step1 := by
      have heq : raw5363step1 = (fun i j => raw5363step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5363step0 permutation27 permutation17
    _ = injectiveMoment H node1107 := by rfl

theorem canonical5366 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5366 = injectiveMoment H node825 := by
  calc
    injectiveMoment H raw5366 = injectiveMoment H raw5366step0 := by
      have heq : raw5366step0 = raw5366.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5366).symm
    injectiveMoment H raw5366step0 = injectiveMoment H raw5366step1 := by
      have heq : raw5366step1 = (fun i j => raw5366step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5366step0 permutation27 permutation17
    _ = injectiveMoment H node825 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5423 = injectiveMoment H node605 := by
  calc
    injectiveMoment H raw5423 = injectiveMoment H raw5423step0 := by
      have heq : raw5423step0 = (fun i j => raw5423 (permutation9 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5423 permutation9 permutation12
    _ = injectiveMoment H node605 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3396 = injectiveMoment H node1357 := by
  calc
    injectiveMoment H raw3396 = injectiveMoment H raw3396step0 := by
      have heq : raw3396step0 = (fun i j => raw3396 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3396 permutation16 permutation17
    _ = injectiveMoment H node1357 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4445 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw4445 = injectiveMoment H raw4445step0 := by
      have heq : raw4445step0 = raw4445.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4445).symm
    injectiveMoment H raw4445step0 = injectiveMoment H raw4445step1 := by
      have heq : raw4445step1 = (fun i j => raw4445step0 (permutation25 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4445step0 permutation25 permutation26
    _ = injectiveMoment H node1304 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3325 = injectiveMoment H node1998 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1998 = Sparse.eval value1998 (momentVector H) := by
  have heq : pivotMatrix1998 = (fun u v => node1998 (pivotPermutation1998 u) v) := by apply Matrix.ext; unfold pivotMatrix1998 node1998 pivotPermutation1998; decide +kernel
  have hmoment : injectiveMoment H node1998 = injectiveMoment H pivotMatrix1998 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1998 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1998 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1998 (0 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (0 : Fin 4) = raw4445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw4445; decide +kernel
    rw [heq]
    exact (canonical4445 hH).trans (sound1304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1998 (1 : Fin 4)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (1 : Fin 4) = raw3396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3396; decide +kernel
    rw [heq]
    exact (canonical3396 hH).trans (sound1357 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1998 (2 : Fin 4)) =
      Sparse.eval value605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (2 : Fin 4) = raw3338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3338; decide +kernel
    rw [heq]
    exact (canonical3338 hH).trans (sound605 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1998 (3 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1998 (3 : Fin 4) = raw3329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1998 raw3329; decide +kernel
    rw [heq]
    exact (canonical3329 hH).trans (sound1304 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1998 + (injectiveMoment H (mergeFirst pivotMatrix1998 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1998 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1998, value1304, value1357, value605, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5225 = injectiveMoment H node789 := by
  calc
    injectiveMoment H raw5225 = injectiveMoment H raw5225step0 := by
      have heq : raw5225step0 = raw5225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5225).symm
    injectiveMoment H raw5225step0 = injectiveMoment H raw5225step1 := by
      have heq : raw5225step1 = (fun i j => raw5225step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5225step0 permutation29 permutation18
    _ = injectiveMoment H node789 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5265 = injectiveMoment H node2341 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound49
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3165 = Sparse.eval value3165 (momentVector H) := by
  have heq : pivotMatrix3165 = (fun u v => node3165 (pivotPermutation3165 u) v) := by apply Matrix.ext; unfold pivotMatrix3165 node3165 pivotPermutation3165; decide +kernel
  have hmoment : injectiveMoment H node3165 = injectiveMoment H pivotMatrix3165 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3165 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3165 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3165 (0 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (0 : Fin 5) = raw2191 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw2191; decide +kernel
    rw [heq]
    exact (canonical2191 hH).trans (sound1746 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3165 (1 : Fin 5)) =
      Sparse.eval value1998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (1 : Fin 5) = raw3325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3325; decide +kernel
    rw [heq]
    exact (canonical3325 hH).trans (sound1998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3165 (2 : Fin 5)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (2 : Fin 5) = raw3382 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3382; decide +kernel
    rw [heq]
    exact (canonical3382 hH).trans (sound1357 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3165 (3 : Fin 5)) =
      Sparse.eval value1357 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (3 : Fin 5) = raw3388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3388; decide +kernel
    rw [heq]
    exact (canonical3388 hH).trans (sound1357 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3165 (4 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3165 (4 : Fin 5) = raw3390 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3165 raw3390; decide +kernel
    rw [heq]
    exact (canonical3390 hH).trans (sound1746 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3165 + (injectiveMoment H (mergeFirst pivotMatrix3165 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3165 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3165, value1357, value1746, value1998, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound36
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2341 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2341 = Sparse.eval value2341 (momentVector H) := by
  have heq : pivotMatrix2341 = (fun u v => node2341 (pivotPermutation2341 u) v) := by apply Matrix.ext; unfold pivotMatrix2341 node2341 pivotPermutation2341; decide +kernel
  have hmoment : injectiveMoment H node2341 = injectiveMoment H pivotMatrix2341 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2341 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2341 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2341 (0 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (0 : Fin 4) = raw5225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5225; decide +kernel
    rw [heq]
    exact (canonical5225 hH).trans (sound789 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2341 (1 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (1 : Fin 4) = raw5281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5281; decide +kernel
    rw [heq]
    exact (canonical5281 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2341 (2 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (2 : Fin 4) = raw5289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5289; decide +kernel
    rw [heq]
    exact (canonical5289 hH).trans (sound1027 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2341 (3 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (3 : Fin 4) = raw5292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5292; decide +kernel
    rw [heq]
    exact (canonical5292 hH).trans (sound825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2341 + (injectiveMoment H (mergeFirst pivotMatrix2341 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2341, value1027, value197, value789, value825, Sparse.eval] at hc ⊢
  linarith

theorem sound2352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2352 = Sparse.eval value2352 (momentVector H) := by
  have heq : pivotMatrix2352 = (fun u v => node2352 (pivotPermutation2352 u) v) := by apply Matrix.ext; unfold pivotMatrix2352 node2352 pivotPermutation2352; decide +kernel
  have hmoment : injectiveMoment H node2352 = injectiveMoment H pivotMatrix2352 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2352 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2352 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2352 (0 : Fin 4)) =
      Sparse.eval value605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (0 : Fin 4) = raw5423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5423; decide +kernel
    rw [heq]
    exact (canonical5423 hH).trans (sound605 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2352 (1 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (1 : Fin 4) = raw5347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5347; decide +kernel
    rw [heq]
    exact (canonical5347 hH).trans (sound1304 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2352 (2 : Fin 4)) =
      Sparse.eval value587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (2 : Fin 4) = raw5325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5325; decide +kernel
    rw [heq]
    exact (canonical5325 hH).trans (sound587 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2352 (3 : Fin 4)) =
      Sparse.eval value719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (3 : Fin 4) = raw5323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5323; decide +kernel
    rw [heq]
    exact (canonical5323 hH).trans (sound719 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2352 + (injectiveMoment H (mergeFirst pivotMatrix2352 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2352, value1304, value587, value605, value719, Sparse.eval] at hc ⊢
  linarith

theorem sound2358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2358 = Sparse.eval value2358 (momentVector H) := by
  have heq : pivotMatrix2358 = (fun u v => node2358 (pivotPermutation2358 u) v) := by apply Matrix.ext; unfold pivotMatrix2358 node2358 pivotPermutation2358; decide +kernel
  have hmoment : injectiveMoment H node2358 = injectiveMoment H pivotMatrix2358 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2358 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2358 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2358 (0 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (0 : Fin 4) = raw5292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5292; decide +kernel
    rw [heq]
    exact (canonical5292 hH).trans (sound825 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2358 (1 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (1 : Fin 4) = raw5355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5355; decide +kernel
    rw [heq]
    exact (canonical5355 hH).trans (sound224 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2358 (2 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (2 : Fin 4) = raw5363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5363; decide +kernel
    rw [heq]
    exact (canonical5363 hH).trans (sound1107 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2358 (3 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (3 : Fin 4) = raw5366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5366; decide +kernel
    rw [heq]
    exact (canonical5366 hH).trans (sound825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2358 + (injectiveMoment H (mergeFirst pivotMatrix2358 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2358, value1107, value224, value825, Sparse.eval] at hc ⊢
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

theorem sound3318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3318 = Sparse.eval value3318 (momentVector H) := by
  have heq : pivotMatrix3318 = (fun u v => node3318 (pivotPermutation3318 u) v) := by apply Matrix.ext; unfold pivotMatrix3318 node3318 pivotPermutation3318; decide +kernel
  have hmoment : injectiveMoment H node3318 = injectiveMoment H pivotMatrix3318 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3318 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3318 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3318 (0 : Fin 5)) =
      Sparse.eval value2341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3318 (0 : Fin 5) = raw5265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3318 raw5265; decide +kernel
    rw [heq]
    exact (canonical5265 hH).trans (sound2341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3318 (1 : Fin 5)) =
      Sparse.eval value2352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3318 (1 : Fin 5) = raw5317 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3318 raw5317; decide +kernel
    rw [heq]
    exact (canonical5317 hH).trans (sound2352 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3318 (2 : Fin 5)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3318 (2 : Fin 5) = raw5338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3318 raw5338; decide +kernel
    rw [heq]
    exact (canonical5338 hH).trans (sound1304 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3318 (3 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3318 (3 : Fin 5) = raw5341 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3318 raw5341; decide +kernel
    rw [heq]
    exact (canonical5341 hH).trans (sound1746 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3318 (4 : Fin 5)) =
      Sparse.eval value2358 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3318 (4 : Fin 5) = raw5342 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3318 raw5342; decide +kernel
    rw [heq]
    exact (canonical5342 hH).trans (sound2358 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3318 + (injectiveMoment H (mergeFirst pivotMatrix3318 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3318 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3318 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3318 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3318 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3318, value1304, value1746, value2341, value2352, value2358, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary6
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound131 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow131 (momentVector H) = 0 := by
  have hshape : boundaryMatrix131 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix131 3 2 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix131 (0 : Fin 6)) =
      Sparse.eval value3318 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (0 : Fin 6) = raw9094 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9094 hH).trans (sound3318 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix131 (1 : Fin 6)) =
      Sparse.eval value3318 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (1 : Fin 6) = raw9224 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9224 hH).trans (sound3318 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix131 (2 : Fin 6)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (2 : Fin 6) = raw9279 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9279 hH).trans (sound1746 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix131 (3 : Fin 6)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (3 : Fin 6) = raw9289 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9289 hH).trans (sound1746 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix131 (4 : Fin 6)) =
      Sparse.eval value3317 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (4 : Fin 6) = raw9290 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9290 hH).trans (sound3317_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix131 (5 : Fin 6)) =
      Sparse.eval value3165 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix131 (5 : Fin 6) = raw9291 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9291 hH).trans (sound3165 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix131 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix131 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow131, value1746, value3165, value3317, value3318, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck103 : Integer.Sparse.reindex coordinateMap (PairData.rows 103) =
    PairSemantics.boundaryRow131 := by decide +kernel

theorem rowSound103_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 103) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck103]
  exact PairSemantics.boundarySound131 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e_oai
