-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3463_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T11:50:20.278601+00:00
-- url     : https://prove2.me/submissions/72be499b-fc38-41a0-9146-c52219b5db48

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
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

end MUB6

end

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

theorem canonical3347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3347 = injectiveMoment H node608 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3406 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3406 = injectiveMoment H raw3406step0 := by
      have heq : raw3406step0 = raw3406.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3406).symm
    injectiveMoment H raw3406step0 = injectiveMoment H raw3406step1 := by
      have heq : raw3406step1 = (fun i j => raw3406step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3406step0 permutation30 permutation24
    _ = injectiveMoment H node1241 := by rfl

theorem canonical3409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3409 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3409 = injectiveMoment H raw3409step0 := by
      have heq : raw3409step0 = raw3409.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3409).symm
    injectiveMoment H raw3409step0 = injectiveMoment H raw3409step1 := by
      have heq : raw3409step1 = (fun i j => raw3409step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3409step0 permutation30 permutation30
    _ = injectiveMoment H node1241 := by rfl

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

theorem canonical5949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5949 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5949 = injectiveMoment H raw5949step0 := by
      have heq : raw5949step0 = raw5949.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5949).symm
    injectiveMoment H raw5949step0 = injectiveMoment H raw5949step1 := by
      have hz : ∀ i, raw5949step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw5949step1 = (fun i j => raw5949step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5949step0 permutation5 hz
    injectiveMoment H raw5949step1 = injectiveMoment H raw5949step2 := by
      have heq : raw5949step2 = (fun i j => raw5949step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5949step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5989 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw5989 = injectiveMoment H raw5989step0 := by
      have heq : raw5989step0 = (fun i j => raw5989 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5989 permutation4 permutation3
    _ = injectiveMoment H node58 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6315 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6315 = injectiveMoment H raw6315step0 := by
      have heq : raw6315step0 = raw6315.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6315).symm
    injectiveMoment H raw6315step0 = injectiveMoment H raw6315step1 := by
      have heq : raw6315step1 = (fun i j => raw6315step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6315step0 permutation22 permutation5
    _ = injectiveMoment H node285 := by rfl

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

theorem canonical6540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6540 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw6540 = injectiveMoment H raw6540step0 := by
      have heq : raw6540step0 = raw6540.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6540).symm
    injectiveMoment H raw6540step0 = injectiveMoment H raw6540step1 := by
      have heq : raw6540step1 = (fun i j => raw6540step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6540step0 permutation22 permutation5
    _ = injectiveMoment H node294 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6832 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6832 = injectiveMoment H raw6832step0 := by
      have heq : raw6832step0 = raw6832.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6832).symm
    injectiveMoment H raw6832step0 = injectiveMoment H raw6832step1 := by
      have hz : ∀ i, raw6832step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw6832step1 = (fun i j => raw6832step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6832step0 permutation5 hz
    injectiveMoment H raw6832step1 = injectiveMoment H raw6832step2 := by
      have heq : raw6832step2 = (fun i j => raw6832step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6832step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical6858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6858 = injectiveMoment H node61 := by
  rfl

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7090 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7090 = injectiveMoment H raw7090step0 := by
      have heq : raw7090step0 = raw7090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7090).symm
    injectiveMoment H raw7090step0 = injectiveMoment H raw7090step1 := by
      have hz : ∀ j, raw7090step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7090step1 = (fun i j => raw7090step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7090step0 permutation15 hz
    injectiveMoment H raw7090step1 = injectiveMoment H raw7090step2 := by
      have hz : ∀ i, raw7090step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7090step2 = (fun i j => raw7090step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7090step1 permutation5 hz
    injectiveMoment H raw7090step2 = injectiveMoment H raw7090step3 := by
      have heq : raw7090step3 = (fun i j => raw7090step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7090step2 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7114 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7114 = injectiveMoment H raw7114step0 := by
      have heq : raw7114step0 = raw7114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7114).symm
    injectiveMoment H raw7114step0 = injectiveMoment H raw7114step1 := by
      have heq : raw7114step1 = (fun i j => raw7114step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7114step0 permutation22 permutation5
    _ = injectiveMoment H node269 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7206 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7206 = injectiveMoment H raw7206step0 := by
      have heq : raw7206step0 = raw7206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7206).symm
    injectiveMoment H raw7206step0 = injectiveMoment H raw7206step1 := by
      have hz : ∀ j, raw7206step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7206step1 = (fun i j => raw7206step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7206step0 permutation15 hz
    injectiveMoment H raw7206step1 = injectiveMoment H raw7206step2 := by
      have hz : ∀ i, raw7206step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7206step2 = (fun i j => raw7206step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7206step1 permutation5 hz
    injectiveMoment H raw7206step2 = injectiveMoment H raw7206step3 := by
      have heq : raw7206step3 = (fun i j => raw7206step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7206step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical7241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7241 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7241 = injectiveMoment H raw7241step0 := by
      have heq : raw7241step0 = raw7241.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7241).symm
    injectiveMoment H raw7241step0 = injectiveMoment H raw7241step1 := by
      have heq : raw7241step1 = (fun i j => raw7241step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7241step0 permutation22 permutation5
    _ = injectiveMoment H node284 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7783 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw7783 = injectiveMoment H raw7783step0 := by
      have heq : raw7783step0 = raw7783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7783).symm
    injectiveMoment H raw7783step0 = injectiveMoment H raw7783step1 := by
      have heq : raw7783step1 = (fun i j => raw7783step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7783step0 permutation29 permutation6
    _ = injectiveMoment H node168 := by rfl

theorem canonical7791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7791 = injectiveMoment H node2839 := by
  rfl

theorem canonical7792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7792 = injectiveMoment H node2839 := by
  calc
    injectiveMoment H raw7792 = injectiveMoment H raw7792step0 := by
      have heq : raw7792step0 = (fun i j => raw7792 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7792 permutation34 permutation9
    _ = injectiveMoment H node2839 := by rfl

theorem canonical7793 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7793 = injectiveMoment H node678 := by
  calc
    injectiveMoment H raw7793 = injectiveMoment H raw7793step0 := by
      have heq : raw7793step0 = raw7793.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7793).symm
    injectiveMoment H raw7793step0 = injectiveMoment H raw7793step1 := by
      have heq : raw7793step1 = (fun i j => raw7793step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7793step0 permutation27 permutation24
    _ = injectiveMoment H node678 := by rfl

theorem canonical7794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7794 = injectiveMoment H node2840 := by
  rfl

theorem canonical7795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7795 = injectiveMoment H node689 := by
  calc
    injectiveMoment H raw7795 = injectiveMoment H raw7795step0 := by
      have heq : raw7795step0 = raw7795.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7795).symm
    injectiveMoment H raw7795step0 = injectiveMoment H raw7795step1 := by
      have heq : raw7795step1 = (fun i j => raw7795step0 (permutation18 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7795step0 permutation18 permutation30
    _ = injectiveMoment H node689 := by rfl

theorem canonical7798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7798 = injectiveMoment H node1330 := by
  calc
    injectiveMoment H raw7798 = injectiveMoment H raw7798step0 := by
      have heq : raw7798step0 = (fun i j => raw7798 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7798 permutation10 permutation9
    _ = injectiveMoment H node1330 := by rfl

theorem canonical7799 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7799 = injectiveMoment H node1359 := by
  calc
    injectiveMoment H raw7799 = injectiveMoment H raw7799step0 := by
      have heq : raw7799step0 = raw7799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7799).symm
    injectiveMoment H raw7799step0 = injectiveMoment H raw7799step1 := by
      have heq : raw7799step1 = (fun i j => raw7799step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7799step0 permutation18 permutation29
    _ = injectiveMoment H node1359 := by rfl

theorem canonical7801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7801 = injectiveMoment H node1746 := by
  calc
    injectiveMoment H raw7801 = injectiveMoment H raw7801step0 := by
      have heq : raw7801step0 = (fun i j => raw7801 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7801 permutation36 permutation21
    _ = injectiveMoment H node1746 := by rfl

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

theorem canonical7816 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7816 = injectiveMoment H node1335 := by
  rfl

theorem canonical7817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7817 = injectiveMoment H node1201 := by
  calc
    injectiveMoment H raw7817 = injectiveMoment H raw7817step0 := by
      have heq : raw7817step0 = raw7817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7817).symm
    injectiveMoment H raw7817step0 = injectiveMoment H raw7817step1 := by
      have heq : raw7817step1 = (fun i j => raw7817step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7817step0 permutation23 permutation19
    _ = injectiveMoment H node1201 := by rfl

theorem canonical7823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7823 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw7823 = injectiveMoment H raw7823step0 := by
      have heq : raw7823step0 = raw7823.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7823).symm
    injectiveMoment H raw7823step0 = injectiveMoment H raw7823step1 := by
      have heq : raw7823step1 = (fun i j => raw7823step0 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7823step0 permutation29 permutation6
    _ = injectiveMoment H node283 := by rfl

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

theorem canonical7832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7832 = injectiveMoment H node2014 := by
  calc
    injectiveMoment H raw7832 = injectiveMoment H raw7832step0 := by
      have heq : raw7832step0 = (fun i j => raw7832 (permutation96 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7832 permutation96 permutation29
    _ = injectiveMoment H node2014 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7848 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw7848 = injectiveMoment H raw7848step0 := by
      have heq : raw7848step0 = raw7848.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7848).symm
    injectiveMoment H raw7848step0 = injectiveMoment H raw7848step1 := by
      have heq : raw7848step1 = (fun i j => raw7848step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7848step0 permutation21 permutation5
    _ = injectiveMoment H node168 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7874 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7874 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw7874 = injectiveMoment H raw7874step0 := by
      have heq : raw7874step0 = raw7874.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7874).symm
    injectiveMoment H raw7874step0 = injectiveMoment H raw7874step1 := by
      have heq : raw7874step1 = (fun i j => raw7874step0 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7874step0 permutation21 permutation3
    _ = injectiveMoment H node259 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8545 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw8545 = injectiveMoment H raw8545step0 := by
      have heq : raw8545step0 = (fun i j => raw8545 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8545 permutation5 permutation4
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8778 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8778 = injectiveMoment H raw8778step0 := by
      have hz : ∀ i, raw8778 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8778step0 = (fun i j => raw8778 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8778 permutation3 hz
    injectiveMoment H raw8778step0 = injectiveMoment H raw8778step1 := by
      have heq : raw8778step1 = (fun i j => raw8778step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8778step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical8880 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8880 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw8880 = injectiveMoment H raw8880step0 := by
      have heq : raw8880step0 = raw8880.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8880).symm
    injectiveMoment H raw8880step0 = injectiveMoment H raw8880step1 := by
      have heq : raw8880step1 = (fun i j => raw8880step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8880step0 permutation19 permutation3
    _ = injectiveMoment H node267 := by rfl

theorem canonical8881 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8881 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw8881 = injectiveMoment H raw8881step0 := by
      have heq : raw8881step0 = raw8881.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8881).symm
    injectiveMoment H raw8881step0 = injectiveMoment H raw8881step1 := by
      have heq : raw8881step1 = (fun i j => raw8881step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8881step0 permutation19 permutation3
    _ = injectiveMoment H node283 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical283
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9083 = injectiveMoment H node1344 := by
  calc
    injectiveMoment H raw9083 = injectiveMoment H raw9083step0 := by
      have heq : raw9083step0 = (fun i j => raw9083 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9083 permutation15 permutation9
    _ = injectiveMoment H node1344 := by rfl

theorem canonical9084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9084 = injectiveMoment H node1345 := by
  calc
    injectiveMoment H raw9084 = injectiveMoment H raw9084step0 := by
      have heq : raw9084step0 = (fun i j => raw9084 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9084 permutation15 permutation9
    _ = injectiveMoment H node1345 := by rfl

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

theorem canonical9230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9230 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw9230 = injectiveMoment H raw9230step0 := by
      have hz : ∀ i, raw9230 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw9230step0 = (fun i j => raw9230 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9230 permutation15 hz
    injectiveMoment H raw9230step0 = injectiveMoment H raw9230step1 := by
      have hz : ∀ i, raw9230step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9230step1 = (fun i j => raw9230step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9230step0 permutation3 hz
    injectiveMoment H raw9230step1 = injectiveMoment H raw9230step2 := by
      have heq : raw9230step2 = (fun i j => raw9230step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9230step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical303
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9699 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw9699 = injectiveMoment H raw9699step0 := by
      have heq : raw9699step0 = raw9699.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9699).symm
    injectiveMoment H raw9699step0 = injectiveMoment H raw9699step1 := by
      have hz : ∀ i, raw9699step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9699step1 = (fun i j => raw9699step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9699step0 permutation3 hz
    injectiveMoment H raw9699step1 = injectiveMoment H raw9699step2 := by
      have heq : raw9699step2 = (fun i j => raw9699step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9699step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10129 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw10129 = injectiveMoment H raw10129step0 := by
      have heq : raw10129step0 = raw10129.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10129).symm
    injectiveMoment H raw10129step0 = injectiveMoment H raw10129step1 := by
      have heq : raw10129step1 = (fun i j => raw10129step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10129step0 permutation19 permutation5
    _ = injectiveMoment H node168 := by rfl

theorem canonical10130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10130 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw10130 = injectiveMoment H raw10130step0 := by
      have heq : raw10130step0 = raw10130.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10130).symm
    injectiveMoment H raw10130step0 = injectiveMoment H raw10130step1 := by
      have heq : raw10130step1 = (fun i j => raw10130step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10130step0 permutation19 permutation5
    _ = injectiveMoment H node283 := by rfl

theorem canonical10132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10132 = injectiveMoment H node258 := by
  calc
    injectiveMoment H raw10132 = injectiveMoment H raw10132step0 := by
      have heq : raw10132step0 = raw10132.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10132).symm
    injectiveMoment H raw10132step0 = injectiveMoment H raw10132step1 := by
      have heq : raw10132step1 = (fun i j => raw10132step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10132step0 permutation19 permutation3
    _ = injectiveMoment H node258 := by rfl

theorem canonical10133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10133 = injectiveMoment H node275 := by
  calc
    injectiveMoment H raw10133 = injectiveMoment H raw10133step0 := by
      have heq : raw10133step0 = raw10133.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10133).symm
    injectiveMoment H raw10133step0 = injectiveMoment H raw10133step1 := by
      have heq : raw10133step1 = (fun i j => raw10133step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10133step0 permutation19 permutation3
    _ = injectiveMoment H node275 := by rfl

theorem canonical10138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10138 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw10138 = injectiveMoment H raw10138step0 := by
      have heq : raw10138step0 = raw10138.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10138).symm
    injectiveMoment H raw10138step0 = injectiveMoment H raw10138step1 := by
      have heq : raw10138step1 = (fun i j => raw10138step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10138step0 permutation32 permutation4
    _ = injectiveMoment H node279 := by rfl

theorem canonical10140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10140 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw10140 = injectiveMoment H raw10140step0 := by
      have heq : raw10140step0 = raw10140.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10140).symm
    injectiveMoment H raw10140step0 = injectiveMoment H raw10140step1 := by
      have heq : raw10140step1 = (fun i j => raw10140step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10140step0 permutation32 permutation4
    _ = injectiveMoment H node291 := by rfl

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

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

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

theorem canonical2204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2204 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw2204 = injectiveMoment H raw2204step0 := by
      have heq : raw2204step0 = raw2204.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2204).symm
    injectiveMoment H raw2204step0 = injectiveMoment H raw2204step1 := by
      have heq : raw2204step1 = (fun i j => raw2204step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2204step0 permutation19 permutation18
    _ = injectiveMoment H node1360 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2783 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw2783 = injectiveMoment H raw2783step0 := by
      have heq : raw2783step0 = raw2783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2783).symm
    injectiveMoment H raw2783step0 = injectiveMoment H raw2783step1 := by
      have hz : ∀ i, raw2783step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw2783step1 = (fun i j => raw2783step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2783step0 permutation5 hz
    injectiveMoment H raw2783step1 = injectiveMoment H raw2783step2 := by
      have heq : raw2783step2 = (fun i j => raw2783step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2783step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node168 = Sparse.eval value168 (momentVector H) := by
  have heq : pivotMatrix168 = (fun u v => node168 (pivotPermutation168 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node168 = injectiveMoment H pivotMatrix168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix168 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (0 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (1 : Fin 3) = raw2783 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2783 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node168 + (injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value168, value10, value52, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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

theorem sound259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node259 = Sparse.eval value259 (momentVector H) := by
  have heq : pivotMatrix259 = (fun u v => node259 (pivotPermutation259 u) v) := by apply Matrix.ext; unfold pivotMatrix259 node259 pivotPermutation259; decide +kernel
  have hmoment : injectiveMoment H node259 = injectiveMoment H pivotMatrix259 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix259 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix259 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix259 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (0 : Fin 3) = raw2861 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw2861; decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix259 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (1 : Fin 3) = raw5949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw5949; decide +kernel
    rw [heq]
    exact (canonical5949 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix259 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix259 (2 : Fin 3) = raw5989 := by apply Matrix.ext; unfold mergeFirst pivotMatrix259 raw5989; decide +kernel
    rw [heq]
    exact (canonical5989 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node259 + (injectiveMoment H (mergeFirst pivotMatrix259 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix259 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix259 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value259, value10, value58, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node267 = Sparse.eval value267 (momentVector H) := by
  have heq : pivotMatrix267 = (fun u v => node267 (pivotPermutation267 u) v) := by apply Matrix.ext; unfold pivotMatrix267 node267 pivotPermutation267; decide +kernel
  have hmoment : injectiveMoment H node267 = injectiveMoment H pivotMatrix267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix267 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix267 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix267 (0 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (0 : Fin 3) = raw5540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5540; decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix267 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (1 : Fin 3) = raw5949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5949; decide +kernel
    rw [heq]
    exact (canonical5949 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix267 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix267 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix267 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node267 + (injectiveMoment H (mergeFirst pivotMatrix267 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix267 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix267 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value267, value10, value51, value56, Sparse.eval] at hc ⊢
  linarith

theorem sound269 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node269 = Sparse.eval value269 (momentVector H) := by
  have heq : pivotMatrix269 = (fun u v => node269 (pivotPermutation269 u) v) := by apply Matrix.ext; unfold pivotMatrix269 node269 pivotPermutation269; decide +kernel
  have hmoment : injectiveMoment H node269 = injectiveMoment H pivotMatrix269 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix269 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix269 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (0 : Fin 3) = raw5550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5550; decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix269 (2 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix269 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node269 + (injectiveMoment H (mergeFirst pivotMatrix269 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix269 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value269, value53, value57, value58, Sparse.eval] at hc ⊢
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

theorem sound283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node283 = Sparse.eval value283 (momentVector H) := by
  have heq : pivotMatrix283 = (fun u v => node283 (pivotPermutation283 u) v) := by apply Matrix.ext; unfold pivotMatrix283 node283 pivotPermutation283; decide +kernel
  have hmoment : injectiveMoment H node283 = injectiveMoment H pivotMatrix283 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix283 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix283 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix283 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (0 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix283 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (1 : Fin 3) = raw6832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw6832; decide +kernel
    rw [heq]
    exact (canonical6832 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix283 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix283 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix283 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node283 + (injectiveMoment H (mergeFirst pivotMatrix283 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix283 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix283 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value283, value11, value56, value61, Sparse.eval] at hc ⊢
  linarith

theorem sound284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node284 = Sparse.eval value284 (momentVector H) := by
  have heq : pivotMatrix284 = (fun u v => node284 (pivotPermutation284 u) v) := by apply Matrix.ext; unfold pivotMatrix284 node284 pivotPermutation284; decide +kernel
  have hmoment : injectiveMoment H node284 = injectiveMoment H pivotMatrix284 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix284 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix284 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (0 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (1 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix284 (2 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix284 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node284 + (injectiveMoment H (mergeFirst pivotMatrix284 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix284 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value284, value57, value61, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node285 = Sparse.eval value285 (momentVector H) := by
  have heq : pivotMatrix285 = (fun u v => node285 (pivotPermutation285 u) v) := by apply Matrix.ext; unfold pivotMatrix285 node285 pivotPermutation285; decide +kernel
  have hmoment : injectiveMoment H node285 = injectiveMoment H pivotMatrix285 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix285 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix285 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (0 : Fin 3) = raw5982 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw5982; decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix285 (2 : Fin 3) = raw6870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix285 raw6870; decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node285 + (injectiveMoment H (mergeFirst pivotMatrix285 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix285 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value285, value58, value62, value63, Sparse.eval] at hc ⊢
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

theorem sound294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node294 = Sparse.eval value294 (momentVector H) := by
  have heq : pivotMatrix294 = (fun u v => node294 (pivotPermutation294 u) v) := by apply Matrix.ext; unfold pivotMatrix294 node294 pivotPermutation294; decide +kernel
  have hmoment : injectiveMoment H node294 = injectiveMoment H pivotMatrix294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (1 : Fin 3) = raw8545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8545; decide +kernel
    rw [heq]
    exact (canonical8545 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (2 : Fin 3) = raw8778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8778; decide +kernel
    rw [heq]
    exact (canonical8778 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node294 + (injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value294, value11, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node678 = Sparse.eval value678 (momentVector H) := by
  have hc : momentVector H 203 = injectiveMoment H node678 := rfl
  simp [value678, Sparse.eval, hc]

theorem sound689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node689 = Sparse.eval value689 (momentVector H) := by
  have hc : momentVector H 216 = injectiveMoment H node689 := rfl
  simp [value689, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1201 = Sparse.eval value1201 (momentVector H) := by
  have heq : pivotMatrix1201 = (fun u v => node1201 (pivotPermutation1201 u) v) := by apply Matrix.ext; unfold pivotMatrix1201 node1201 pivotPermutation1201; decide +kernel
  have hmoment : injectiveMoment H node1201 = injectiveMoment H pivotMatrix1201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1201 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1201 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1201 (0 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (0 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1201 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (1 : Fin 3) = raw7090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw7090; decide +kernel
    rw [heq]
    exact (canonical7090 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1201 (2 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1201 (2 : Fin 3) = raw7114 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1201 raw7114; decide +kernel
    rw [heq]
    exact (canonical7114 hH).trans (sound269 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1201 + (injectiveMoment H (mergeFirst pivotMatrix1201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1201, value10, value269, value285, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound19
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1241 = Sparse.eval value1241 (momentVector H) := by
  have heq : pivotMatrix1241 = (fun u v => node1241 (pivotPermutation1241 u) v) := by apply Matrix.ext; unfold pivotMatrix1241 node1241 pivotPermutation1241; decide +kernel
  have hmoment : injectiveMoment H node1241 = injectiveMoment H pivotMatrix1241 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1241 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1241 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1241 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (0 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1241 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (1 : Fin 3) = raw7206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw7206; decide +kernel
    rw [heq]
    exact (canonical7206 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1241 (2 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1241 (2 : Fin 3) = raw7241 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1241 raw7241; decide +kernel
    rw [heq]
    exact (canonical7241 hH).trans (sound284 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1241 + (injectiveMoment H (mergeFirst pivotMatrix1241 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1241 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1241 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1241, value11, value284, value294, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1330 = Sparse.eval value1330 (momentVector H) := by
  have hc : momentVector H 253 = injectiveMoment H node1330 := rfl
  simp [value1330, Sparse.eval, hc]

theorem sound1335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1335 = Sparse.eval value1335 (momentVector H) := by
  have heq : pivotMatrix1335 = (fun u v => node1335 (pivotPermutation1335 u) v) := by apply Matrix.ext; unfold pivotMatrix1335 node1335 pivotPermutation1335; decide +kernel
  have hmoment : injectiveMoment H node1335 = injectiveMoment H pivotMatrix1335 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1335 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1335 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1335 (0 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (0 : Fin 3) = raw7783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7783; decide +kernel
    rw [heq]
    exact (canonical7783 hH).trans (sound168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1335 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (1 : Fin 3) = raw7823 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7823; decide +kernel
    rw [heq]
    exact (canonical7823 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1335 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1335 (2 : Fin 3) = raw7824 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1335 raw7824; decide +kernel
    rw [heq]
    exact (canonical7824 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1335 + (injectiveMoment H (mergeFirst pivotMatrix1335 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1335 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1335 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1335, value168, value283, value291, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound9
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node608 = Sparse.eval value608 (momentVector H) := by
  have hc : momentVector H 17 = injectiveMoment H node608 := rfl
  simp [value608, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound21
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1344 = Sparse.eval value1344 (momentVector H) := by
  have heq : pivotMatrix1344 = (fun u v => node1344.transpose (pivotPermutation1344 u) v) := by apply Matrix.ext; unfold pivotMatrix1344 node1344 pivotPermutation1344; decide +kernel
  have hmoment : injectiveMoment H node1344 = injectiveMoment H pivotMatrix1344 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1344 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1344 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1344 (0 : Fin 3)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (0 : Fin 3) = raw9699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw9699; decide +kernel
    rw [heq]
    exact (canonical9699 hH).trans (sound46 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1344 (1 : Fin 3)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (1 : Fin 3) = raw10138 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw10138; decide +kernel
    rw [heq]
    exact (canonical10138 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1344 (2 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1344 (2 : Fin 3) = raw10140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1344 raw10140; decide +kernel
    rw [heq]
    exact (canonical10140 hH).trans (sound291 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1344 + (injectiveMoment H (mergeFirst pivotMatrix1344 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1344 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1344 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1344, value279, value291, value46, Sparse.eval] at hc ⊢
  linarith

theorem sound1345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1345 = Sparse.eval value1345 (momentVector H) := by
  have heq : pivotMatrix1345 = (fun u v => node1345 (pivotPermutation1345 u) v) := by apply Matrix.ext; unfold pivotMatrix1345 node1345 pivotPermutation1345; decide +kernel
  have hmoment : injectiveMoment H node1345 = injectiveMoment H pivotMatrix1345 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1345 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1345 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1345 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (0 : Fin 3) = raw9230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw9230; decide +kernel
    rw [heq]
    exact (canonical9230 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1345 (1 : Fin 3)) =
      Sparse.eval value259 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (1 : Fin 3) = raw7874 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw7874; decide +kernel
    rw [heq]
    exact (canonical7874 hH).trans (sound259 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1345 (2 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1345 (2 : Fin 3) = raw7848 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1345 raw7848; decide +kernel
    rw [heq]
    exact (canonical7848 hH).trans (sound168 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1345 + (injectiveMoment H (mergeFirst pivotMatrix1345 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1345 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1345 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1345, value10, value168, value259, Sparse.eval] at hc ⊢
  linarith

theorem sound1359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1359 = Sparse.eval value1359 (momentVector H) := by
  have heq : pivotMatrix1359 = (fun u v => node1359.transpose (pivotPermutation1359 u) v) := by apply Matrix.ext; unfold pivotMatrix1359 node1359 pivotPermutation1359; decide +kernel
  have hmoment : injectiveMoment H node1359 = injectiveMoment H pivotMatrix1359 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1359 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1359 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1359 (0 : Fin 3)) =
      Sparse.eval value267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (0 : Fin 3) = raw8880 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw8880; decide +kernel
    rw [heq]
    exact (canonical8880 hH).trans (sound267 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1359 (1 : Fin 3)) =
      Sparse.eval value168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (1 : Fin 3) = raw10129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw10129; decide +kernel
    rw [heq]
    exact (canonical10129 hH).trans (sound168 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1359 (2 : Fin 3)) =
      Sparse.eval value258 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1359 (2 : Fin 3) = raw10132 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1359 raw10132; decide +kernel
    rw [heq]
    exact (canonical10132 hH).trans (sound258 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1359 + (injectiveMoment H (mergeFirst pivotMatrix1359 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1359 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1359 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1359, value168, value258, value267, Sparse.eval] at hc ⊢
  linarith

theorem sound1360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1360 = Sparse.eval value1360 (momentVector H) := by
  have heq : pivotMatrix1360 = (fun u v => node1360.transpose (pivotPermutation1360 u) v) := by apply Matrix.ext; unfold pivotMatrix1360 node1360 pivotPermutation1360; decide +kernel
  have hmoment : injectiveMoment H node1360 = injectiveMoment H pivotMatrix1360 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1360 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1360 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1360 (0 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (0 : Fin 3) = raw8881 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw8881; decide +kernel
    rw [heq]
    exact (canonical8881 hH).trans (sound283 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1360 (1 : Fin 3)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (1 : Fin 3) = raw10130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw10130; decide +kernel
    rw [heq]
    exact (canonical10130 hH).trans (sound283 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1360 (2 : Fin 3)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1360 (2 : Fin 3) = raw10133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1360 raw10133; decide +kernel
    rw [heq]
    exact (canonical10133 hH).trans (sound275 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1360 + (injectiveMoment H (mergeFirst pivotMatrix1360 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1360 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1360 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1360, value275, value283, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound31
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2014 = Sparse.eval value2014 (momentVector H) := by
  have heq : pivotMatrix2014 = (fun u v => node2014 (pivotPermutation2014 u) v) := by apply Matrix.ext; unfold pivotMatrix2014 node2014 pivotPermutation2014; decide +kernel
  have hmoment : injectiveMoment H node2014 = injectiveMoment H pivotMatrix2014 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2014 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2014 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2014 (0 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (0 : Fin 4) = raw2204 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw2204; decide +kernel
    rw [heq]
    exact (canonical2204 hH).trans (sound1360 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2014 (1 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (1 : Fin 4) = raw3347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3347; decide +kernel
    rw [heq]
    exact (canonical3347 hH).trans (sound608 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2014 (2 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (2 : Fin 4) = raw3406 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3406; decide +kernel
    rw [heq]
    exact (canonical3406 hH).trans (sound1241 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2014 (3 : Fin 4)) =
      Sparse.eval value1241 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2014 (3 : Fin 4) = raw3409 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2014 raw3409; decide +kernel
    rw [heq]
    exact (canonical3409 hH).trans (sound1241 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2014 + (injectiveMoment H (mergeFirst pivotMatrix2014 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2014 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2014, value1241, value1360, value608, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound44
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2839 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2839 = Sparse.eval value2839 (momentVector H) := by
  have heq : pivotMatrix2839 = (fun u v => node2839 (pivotPermutation2839 u) v) := by apply Matrix.ext; unfold pivotMatrix2839 node2839 pivotPermutation2839; decide +kernel
  have hmoment : injectiveMoment H node2839 = injectiveMoment H pivotMatrix2839 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2839 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2839 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2839 (0 : Fin 4)) =
      Sparse.eval value1344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2839 (0 : Fin 4) = raw9083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2839 raw9083; decide +kernel
    rw [heq]
    exact (canonical9083 hH).trans (sound1344 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2839 (1 : Fin 4)) =
      Sparse.eval value1335 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2839 (1 : Fin 4) = raw7816 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2839 raw7816; decide +kernel
    rw [heq]
    exact (canonical7816 hH).trans (sound1335 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2839 (2 : Fin 4)) =
      Sparse.eval value1330 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2839 (2 : Fin 4) = raw7798 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2839 raw7798; decide +kernel
    rw [heq]
    exact (canonical7798 hH).trans (sound1330 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2839 (3 : Fin 4)) =
      Sparse.eval value678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2839 (3 : Fin 4) = raw7793 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2839 raw7793; decide +kernel
    rw [heq]
    exact (canonical7793 hH).trans (sound678 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2839 + (injectiveMoment H (mergeFirst pivotMatrix2839 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2839 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2839 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2839 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2839, value1330, value1335, value1344, value678, Sparse.eval] at hc ⊢
  linarith

theorem sound2840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2840 = Sparse.eval value2840 (momentVector H) := by
  have heq : pivotMatrix2840 = (fun u v => node2840 (pivotPermutation2840 u) v) := by apply Matrix.ext; unfold pivotMatrix2840 node2840 pivotPermutation2840; decide +kernel
  have hmoment : injectiveMoment H node2840 = injectiveMoment H pivotMatrix2840 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2840 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2840 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2840 (0 : Fin 4)) =
      Sparse.eval value1345 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2840 (0 : Fin 4) = raw9084 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2840 raw9084; decide +kernel
    rw [heq]
    exact (canonical9084 hH).trans (sound1345 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2840 (1 : Fin 4)) =
      Sparse.eval value1201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2840 (1 : Fin 4) = raw7817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2840 raw7817; decide +kernel
    rw [heq]
    exact (canonical7817 hH).trans (sound1201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2840 (2 : Fin 4)) =
      Sparse.eval value1359 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2840 (2 : Fin 4) = raw7799 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2840 raw7799; decide +kernel
    rw [heq]
    exact (canonical7799 hH).trans (sound1359 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2840 (3 : Fin 4)) =
      Sparse.eval value689 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2840 (3 : Fin 4) = raw7795 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2840 raw7795; decide +kernel
    rw [heq]
    exact (canonical7795 hH).trans (sound689 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2840 + (injectiveMoment H (mergeFirst pivotMatrix2840 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2840 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2840 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2840 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2840, value1201, value1345, value1359, value689, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound54
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3463_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3463 = Sparse.eval value3463 (momentVector H) := by
  have heq : pivotMatrix3463 = (fun u v => node3463 (pivotPermutation3463 u) v) := by apply Matrix.ext; unfold pivotMatrix3463 node3463 pivotPermutation3463; decide +kernel
  have hmoment : injectiveMoment H node3463 = injectiveMoment H pivotMatrix3463 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3463 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3463 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3463 (0 : Fin 5)) =
      Sparse.eval value2014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (0 : Fin 5) = raw7832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7832; decide +kernel
    rw [heq]
    exact (canonical7832 hH).trans (sound2014 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3463 (1 : Fin 5)) =
      Sparse.eval value1746 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (1 : Fin 5) = raw7801 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7801; decide +kernel
    rw [heq]
    exact (canonical7801 hH).trans (sound1746 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3463 (2 : Fin 5)) =
      Sparse.eval value2840 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (2 : Fin 5) = raw7794 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7794; decide +kernel
    rw [heq]
    exact (canonical7794 hH).trans (sound2840 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3463 (3 : Fin 5)) =
      Sparse.eval value2839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (3 : Fin 5) = raw7792 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7792; decide +kernel
    rw [heq]
    exact (canonical7792 hH).trans (sound2839 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3463 (4 : Fin 5)) =
      Sparse.eval value2839 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3463 (4 : Fin 5) = raw7791 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3463 raw7791; decide +kernel
    rw [heq]
    exact (canonical7791 hH).trans (sound2839 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3463 + (injectiveMoment H (mergeFirst pivotMatrix3463 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3463 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3463, value1746, value2014, value2839, value2840, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3463_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3463_e_oai
