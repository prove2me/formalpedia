-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:27:46.071204+00:00
-- url     : https://prove2.me/submissions/8e336ee2-4c60-4c6a-a5fe-e4b709460c28

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5120 = injectiveMoment H node717 := by
  rfl

theorem canonical5128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5128 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5128 = injectiveMoment H raw5128step0 := by
      have hz : ∀ j, raw5128 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5128step0 = (fun i j => raw5128 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5128 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5136 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5136 = injectiveMoment H raw5136step0 := by
      have hz : ∀ j, raw5136 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5136step0 = (fun i j => raw5136 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5136 permutation104 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5139 = injectiveMoment H node232 := by
  rfl

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

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

theorem canonical7624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7624 = injectiveMoment H node717 := by
  calc
    injectiveMoment H raw7624 = injectiveMoment H raw7624step0 := by
      have heq : raw7624step0 = (fun i j => raw7624 (permutation202 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7624 permutation202 permutation1
    _ = injectiveMoment H node717 := by rfl

theorem canonical7634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7634 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7634 = injectiveMoment H raw7634step0 := by
      have heq : raw7634step0 = (fun i j => raw7634 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7634 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

theorem canonical7646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7646 = injectiveMoment H node717 := by
  calc
    injectiveMoment H raw7646 = injectiveMoment H raw7646step0 := by
      have heq : raw7646step0 = (fun i j => raw7646 (permutation221 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7646 permutation221 permutation1
    _ = injectiveMoment H node717 := by rfl

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

theorem canonical7654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7654 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7654 = injectiveMoment H raw7654step0 := by
      have hz : ∀ j, raw7654 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7654step0 = (fun i j => raw7654 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7654 permutation241 hz
    injectiveMoment H raw7654step0 = injectiveMoment H raw7654step1 := by
      have heq : raw7654step1 = (fun i j => raw7654step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7654step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

theorem canonical7657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7657 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7657 = injectiveMoment H raw7657step0 := by
      have hz : ∀ j, raw7657 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7657step0 = (fun i j => raw7657 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7657 permutation258 hz
    injectiveMoment H raw7657step0 = injectiveMoment H raw7657step1 := by
      have heq : raw7657step1 = (fun i j => raw7657step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7657step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

theorem canonical7658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7658 = injectiveMoment H node1323 := by
  rfl

theorem canonical7670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7670 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7670 = injectiveMoment H raw7670step0 := by
      have hz : ∀ j, raw7670 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7670step0 = (fun i j => raw7670 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7670 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7677 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7677 = injectiveMoment H raw7677step0 := by
      have hz : ∀ j, raw7677 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7677step0 = (fun i j => raw7677 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7677 permutation104 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7679 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7679 = injectiveMoment H raw7679step0 := by
      have hz : ∀ j, raw7679 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7679step0 = (fun i j => raw7679 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7679 permutation128 hz
    _ = injectiveMoment H node65 := by rfl

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

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical5110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5110 = injectiveMoment H node231 := by
  rfl

theorem canonical5112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5112 = injectiveMoment H node25 := by
  calc
    injectiveMoment H raw5112 = injectiveMoment H raw5112step0 := by
      have heq : raw5112step0 = (fun i j => raw5112 (permutation31 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5112 permutation31 permutation2
    _ = injectiveMoment H node25 := by rfl

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

theorem sound231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node231 = Sparse.eval value231 (momentVector H) := by
  have heq : pivotMatrix231 = (fun u v => node231 (pivotPermutation231 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node231 = injectiveMoment H pivotMatrix231 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix231 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix231 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix231 (0 : Fin 4)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (0 : Fin 4) = raw7636 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7636 hH).trans (sound46 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix231 (1 : Fin 4)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (1 : Fin 4) = raw5141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5141 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix231 (2 : Fin 4)) =
      Sparse.eval value45 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (2 : Fin 4) = raw5116 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5116 hH).trans (sound45 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix231 (3 : Fin 4)) =
      Sparse.eval value25 (momentVector H) := by
    have heq : mergeFirst pivotMatrix231 (3 : Fin 4) = raw5112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5112 hH).trans (sound25 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node231 + (injectiveMoment H (mergeFirst pivotMatrix231 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix231 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value231, value25, value45, value46, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical867 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw867 = injectiveMoment H node118 := by
  rfl

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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

theorem sound118 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node118 = Sparse.eval value118 (momentVector H) := by
  have heq : pivotMatrix118 = (fun u v => node118 (pivotPermutation118 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node118 = injectiveMoment H pivotMatrix118 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix118 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix118 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) =
      Sparse.eval value16 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (0 : Fin 4) = raw208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical208 hH).trans (sound16 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (1 : Fin 4) = raw895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical895 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (2 : Fin 4) = raw909 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical909 hH).trans (sound10 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)) =
      Sparse.eval value26 (momentVector H) := by
    have heq : mergeFirst pivotMatrix118 (3 : Fin 4) = raw914 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical914 hH).trans (sound26 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node118 + (injectiveMoment H (mergeFirst pivotMatrix118 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix118 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value118, value10, value16, value26, Sparse.eval] at hc ⊢
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

theorem sound717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node717 = Sparse.eval value717 (momentVector H) := by
  have heq : pivotMatrix717 = (fun u v => node717 (pivotPermutation717 u) v) := by apply Matrix.ext; unfold pivotMatrix717 node717 pivotPermutation717; decide +kernel
  have hmoment : injectiveMoment H node717 = injectiveMoment H pivotMatrix717 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix717 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix717 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix717 (0 : Fin 5)) =
      Sparse.eval value118 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (0 : Fin 5) = raw867 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw867; decide +kernel
    rw [heq]
    exact (canonical867 hH).trans (sound118 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix717 (1 : Fin 5)) =
      Sparse.eval value231 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (1 : Fin 5) = raw5110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5110; decide +kernel
    rw [heq]
    exact (canonical5110 hH).trans (sound231 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix717 (2 : Fin 5)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (2 : Fin 5) = raw5128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5128; decide +kernel
    rw [heq]
    exact (canonical5128 hH).trans (sound46 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix717 (3 : Fin 5)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (3 : Fin 5) = raw5136 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5136; decide +kernel
    rw [heq]
    exact (canonical5136 hH).trans (sound46 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix717 (4 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix717 (4 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix717 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node717 + (injectiveMoment H (mergeFirst pivotMatrix717 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix717 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value717, value118, value231, value232, value46, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1323 = Sparse.eval value1323 (momentVector H) := by
  have heq : pivotMatrix1323 = (fun u v => node1323 (pivotPermutation1323 u) v) := by apply Matrix.ext; unfold pivotMatrix1323 node1323 pivotPermutation1323; decide +kernel
  have hmoment : injectiveMoment H node1323 = injectiveMoment H pivotMatrix1323 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1323 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix1323 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1323 (0 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (0 : Fin 5) = raw5139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw5139; decide +kernel
    rw [heq]
    exact (canonical5139 hH).trans (sound232 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1323 (1 : Fin 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (1 : Fin 5) = raw7634 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7634; decide +kernel
    rw [heq]
    exact (canonical7634 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1323 (2 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (2 : Fin 5) = raw7670 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7670; decide +kernel
    rw [heq]
    exact (canonical7670 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1323 (3 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (3 : Fin 5) = raw7677 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7677; decide +kernel
    rw [heq]
    exact (canonical7677 hH).trans (sound65 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix1323 (4 : Fin 5)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1323 (4 : Fin 5) = raw7679 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1323 raw7679; decide +kernel
    rw [heq]
    exact (canonical7679 hH).trans (sound65 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node1323 + (injectiveMoment H (mergeFirst pivotMatrix1323 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix1323 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value1323, value232, value65, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow1 (momentVector H) = 0 := by
  have hshape : boundaryMatrix1 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix1 1 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix1 (0 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (0 : Fin 6) = raw5120 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5120 hH).trans (sound717 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix1 (1 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (1 : Fin 6) = raw7624 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7624 hH).trans (sound717 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix1 (2 : Fin 6)) =
      Sparse.eval value717 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (2 : Fin 6) = raw7646 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7646 hH).trans (sound717 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix1 (3 : Fin 6)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (3 : Fin 6) = raw7654 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7654 hH).trans (sound232 hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix1 (4 : Fin 6)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (4 : Fin 6) = raw7657 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7657 hH).trans (sound232 hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix1 (5 : Fin 6)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix1 (5 : Fin 6) = raw7658 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7658 hH).trans (sound1323 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix1 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix1 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow1, value1323, value232, value717, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Rows0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck1 : Integer.Sparse.reindex coordinateMap (PairData.rows 1) =
    PairSemantics.boundaryRow1 := by decide +kernel

theorem rowSound1_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 1) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck1]
  exact PairSemantics.boundarySound1 hH

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e_oai
