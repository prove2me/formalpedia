-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3362_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T10:19:03.352835+00:00
-- url     : https://prove2.me/submissions/a7970810-dbc2-410b-af70-e7031a3ef440

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1768_e

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

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3509 = injectiveMoment H node979 := by
  calc
    injectiveMoment H raw3509 = injectiveMoment H raw3509step0 := by
      have heq : raw3509step0 = -raw3509 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3509).symm
    injectiveMoment H raw3509step0 = injectiveMoment H raw3509step1 := by
      have heq : raw3509step1 = (fun i j => raw3509step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3509step0 permutation29 permutation16
    _ = injectiveMoment H node979 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3600 = injectiveMoment H node590 := by
  calc
    injectiveMoment H raw3600 = injectiveMoment H raw3600step0 := by
      have heq : raw3600step0 = raw3600.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3600).symm
    injectiveMoment H raw3600step0 = injectiveMoment H raw3600step1 := by
      have heq : raw3600step1 = -raw3600step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3600step0).symm
    injectiveMoment H raw3600step1 = injectiveMoment H raw3600step2 := by
      have heq : raw3600step2 = (fun i j => raw3600step1 (permutation32 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3600step1 permutation32 permutation12
    _ = injectiveMoment H node590 := by rfl

theorem canonical3602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3602 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw3602 = injectiveMoment H raw3602step0 := by
      have heq : raw3602step0 = -raw3602 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3602).symm
    injectiveMoment H raw3602step0 = injectiveMoment H raw3602step1 := by
      have heq : raw3602step1 = (fun i j => raw3602step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3602step0 permutation16 permutation17
    _ = injectiveMoment H node807 := by rfl

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5044 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw5044 = injectiveMoment H raw5044step0 := by
      have heq : raw5044step0 = raw5044.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5044).symm
    injectiveMoment H raw5044step0 = injectiveMoment H raw5044step1 := by
      have heq : raw5044step1 = (fun i j => raw5044step0 (permutation14 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5044step0 permutation14 permutation4
    _ = injectiveMoment H node229 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5695 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5695 = injectiveMoment H raw5695step0 := by
      have heq : raw5695step0 = raw5695.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5695).symm
    injectiveMoment H raw5695step0 = injectiveMoment H raw5695step1 := by
      have heq : raw5695step1 = (fun i j => raw5695step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5695step0 permutation27 permutation6
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5729 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw5729 = injectiveMoment H raw5729step0 := by
      have heq : raw5729step0 = raw5729.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5729).symm
    injectiveMoment H raw5729step0 = injectiveMoment H raw5729step1 := by
      have heq : raw5729step1 = (fun i j => raw5729step0 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5729step0 permutation30 permutation6
    _ = injectiveMoment H node185 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical582 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw582 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw582 = injectiveMoment H raw582step0 := by
      have heq : raw582step0 = -raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw582).symm
    injectiveMoment H raw582step0 = injectiveMoment H raw582step1 := by
      have heq : raw582step1 = (fun i j => raw582step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw582step0 permutation5 permutation5
    _ = injectiveMoment H node37 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6147 = injectiveMoment H node2517 := by
  rfl

theorem canonical6148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6148 = injectiveMoment H node2545 := by
  calc
    injectiveMoment H raw6148 = injectiveMoment H raw6148step0 := by
      have heq : raw6148step0 = (fun i j => raw6148 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6148 permutation36 permutation15
    _ = injectiveMoment H node2545 := by rfl

theorem canonical6153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6153 = injectiveMoment H node2020 := by
  calc
    injectiveMoment H raw6153 = injectiveMoment H raw6153step0 := by
      have heq : raw6153step0 = -raw6153 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6153).symm
    injectiveMoment H raw6153step0 = injectiveMoment H raw6153step1 := by
      have heq : raw6153step1 = (fun i j => raw6153step0 (permutation101 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6153step0 permutation101 permutation16
    _ = injectiveMoment H node2020 := by rfl

theorem canonical6157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6157 = injectiveMoment H node1018 := by
  calc
    injectiveMoment H raw6157 = injectiveMoment H raw6157step0 := by
      have heq : raw6157step0 = raw6157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6157).symm
    injectiveMoment H raw6157step0 = injectiveMoment H raw6157step1 := by
      have heq : raw6157step1 = (fun i j => raw6157step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6157step0 permutation18 permutation21
    _ = injectiveMoment H node1018 := by rfl

theorem canonical6159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6159 = injectiveMoment H node949 := by
  calc
    injectiveMoment H raw6159 = injectiveMoment H raw6159step0 := by
      have heq : raw6159step0 = (fun i j => raw6159 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6159 permutation9 permutation15
    _ = injectiveMoment H node949 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6187 = injectiveMoment H node1768 := by
  calc
    injectiveMoment H raw6187 = injectiveMoment H raw6187step0 := by
      have heq : raw6187step0 = -raw6187 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6187).symm
    injectiveMoment H raw6187step0 = injectiveMoment H raw6187step1 := by
      have heq : raw6187step1 = (fun i j => raw6187step0 (permutation79 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6187step0 permutation79 permutation23
    _ = injectiveMoment H node1768 := by rfl

theorem canonical6190 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6190 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw6190 = injectiveMoment H raw6190step0 := by
      have heq : raw6190step0 = raw6190.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6190).symm
    injectiveMoment H raw6190step0 = injectiveMoment H raw6190step1 := by
      have heq : raw6190step1 = -raw6190step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6190step0).symm
    injectiveMoment H raw6190step1 = injectiveMoment H raw6190step2 := by
      have heq : raw6190step2 = (fun i j => raw6190step1 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6190step1 permutation14 permutation25
    _ = injectiveMoment H node1123 := by rfl

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

theorem canonical6228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6228 = injectiveMoment H node950 := by
  rfl

theorem canonical6230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6230 = injectiveMoment H node952 := by
  rfl

theorem canonical6232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6232 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6232 = injectiveMoment H raw6232step0 := by
      have heq : raw6232step0 = raw6232.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6232).symm
    injectiveMoment H raw6232step0 = injectiveMoment H raw6232step1 := by
      have heq : raw6232step1 = -raw6232step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6232step0).symm
    injectiveMoment H raw6232step1 = injectiveMoment H raw6232step2 := by
      have heq : raw6232step2 = (fun i j => raw6232step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6232step1 permutation21 permutation5
    _ = injectiveMoment H node109 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6288 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw6288 = injectiveMoment H raw6288step0 := by
      have heq : raw6288step0 = (fun i j => raw6288 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6288 permutation10 permutation15
    _ = injectiveMoment H node974 := by rfl

theorem canonical6292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6292 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6292 = injectiveMoment H raw6292step0 := by
      have heq : raw6292step0 = raw6292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6292).symm
    injectiveMoment H raw6292step0 = injectiveMoment H raw6292step1 := by
      have heq : raw6292step1 = (fun i j => raw6292step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6292step0 permutation27 permutation6
    _ = injectiveMoment H node176 := by rfl

theorem canonical6298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6298 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6298 = injectiveMoment H raw6298step0 := by
      have heq : raw6298step0 = raw6298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6298).symm
    injectiveMoment H raw6298step0 = injectiveMoment H raw6298step1 := by
      have heq : raw6298step1 = (fun i j => raw6298step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6298step0 permutation25 permutation7
    _ = injectiveMoment H node188 := by rfl

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

theorem canonical6326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6326 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6326 = injectiveMoment H raw6326step0 := by
      have heq : raw6326step0 = raw6326.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6326).symm
    injectiveMoment H raw6326step0 = injectiveMoment H raw6326step1 := by
      have heq : raw6326step1 = (fun i j => raw6326step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6326step0 permutation30 permutation8
    _ = injectiveMoment H node271 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6336 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6336 = injectiveMoment H raw6336step0 := by
      have heq : raw6336step0 = raw6336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6336).symm
    injectiveMoment H raw6336step0 = injectiveMoment H raw6336step1 := by
      have heq : raw6336step1 = (fun i j => raw6336step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6336step0 permutation22 permutation7
    _ = injectiveMoment H node170 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6630 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw6630 = injectiveMoment H raw6630step0 := by
      have heq : raw6630step0 = raw6630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6630).symm
    injectiveMoment H raw6630step0 = injectiveMoment H raw6630step1 := by
      have heq : raw6630step1 = -raw6630step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6630step0).symm
    injectiveMoment H raw6630step1 = injectiveMoment H raw6630step2 := by
      have heq : raw6630step2 = (fun i j => raw6630step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6630step1 permutation31 permutation3
    _ = injectiveMoment H node248 := by rfl

theorem canonical6640 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6640 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6640 = injectiveMoment H raw6640step0 := by
      have heq : raw6640step0 = raw6640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6640).symm
    injectiveMoment H raw6640step0 = injectiveMoment H raw6640step1 := by
      have heq : raw6640step1 = -raw6640step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6640step0).symm
    injectiveMoment H raw6640step1 = injectiveMoment H raw6640step2 := by
      have heq : raw6640step2 = (fun i j => raw6640step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6640step1 permutation27 permutation5
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6687 = injectiveMoment H node1124 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6688 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw6688 = injectiveMoment H raw6688step0 := by
      have heq : raw6688step0 = raw6688.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6688).symm
    injectiveMoment H raw6688step0 = injectiveMoment H raw6688step1 := by
      have heq : raw6688step1 = -raw6688step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6688step0).symm
    injectiveMoment H raw6688step1 = injectiveMoment H raw6688step2 := by
      have heq : raw6688step2 = (fun i j => raw6688step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6688step1 permutation32 permutation3
    _ = injectiveMoment H node263 := by rfl

theorem canonical6717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6717 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw6717 = injectiveMoment H raw6717step0 := by
      have heq : raw6717step0 = raw6717.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6717).symm
    injectiveMoment H raw6717step0 = injectiveMoment H raw6717step1 := by
      have heq : raw6717step1 = -raw6717step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6717step0).symm
    injectiveMoment H raw6717step1 = injectiveMoment H raw6717step2 := by
      have heq : raw6717step2 = (fun i j => raw6717step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6717step1 permutation31 permutation3
    _ = injectiveMoment H node263 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6961 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6961 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6961 = injectiveMoment H raw6961step0 := by
      have heq : raw6961step0 = raw6961.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6961).symm
    injectiveMoment H raw6961step0 = injectiveMoment H raw6961step1 := by
      have heq : raw6961step1 = -raw6961step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6961step0).symm
    injectiveMoment H raw6961step1 = injectiveMoment H raw6961step2 := by
      have heq : raw6961step2 = (fun i j => raw6961step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6961step1 permutation19 permutation5
    _ = injectiveMoment H node109 := by rfl

theorem canonical6969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6969 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6969 = injectiveMoment H raw6969step0 := by
      have heq : raw6969step0 = raw6969.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6969).symm
    injectiveMoment H raw6969step0 = injectiveMoment H raw6969step1 := by
      have heq : raw6969step1 = -raw6969step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6969step0).symm
    injectiveMoment H raw6969step1 = injectiveMoment H raw6969step2 := by
      have heq : raw6969step2 = (fun i j => raw6969step1 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6969step1 permutation16 permutation5
    _ = injectiveMoment H node109 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7048 = injectiveMoment H node2773 := by
  calc
    injectiveMoment H raw7048 = injectiveMoment H raw7048step0 := by
      have heq : raw7048step0 = -raw7048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7048).symm
    injectiveMoment H raw7048step0 = injectiveMoment H raw7048step1 := by
      have heq : raw7048step1 = (fun i j => raw7048step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7048step0 permutation98 permutation16
    _ = injectiveMoment H node2773 := by rfl

theorem canonical7051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7051 = injectiveMoment H node1124 := by
  calc
    injectiveMoment H raw7051 = injectiveMoment H raw7051step0 := by
      have heq : raw7051step0 = -raw7051 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7051).symm
    injectiveMoment H raw7051step0 = injectiveMoment H raw7051step1 := by
      have heq : raw7051step1 = (fun i j => raw7051step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7051step0 permutation29 permutation15
    _ = injectiveMoment H node1124 := by rfl

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

theorem canonical7087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7087 = injectiveMoment H node1212 := by
  rfl

theorem canonical7089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7089 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw7089 = injectiveMoment H raw7089step0 := by
      have heq : raw7089step0 = raw7089.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7089).symm
    injectiveMoment H raw7089step0 = injectiveMoment H raw7089step1 := by
      have heq : raw7089step1 = (fun i j => raw7089step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7089step0 permutation25 permutation7
    _ = injectiveMoment H node263 := by rfl

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

theorem canonical7106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7106 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7106 = injectiveMoment H raw7106step0 := by
      have hz : ∀ i, raw7106 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7106step0 = (fun i j => raw7106 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7106 permutation15 hz
    _ = injectiveMoment H node57 := by rfl

theorem canonical7108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7108 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7108 = injectiveMoment H raw7108step0 := by
      have hz : ∀ i, raw7108 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7108step0 = (fun i j => raw7108 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7108 permutation15 hz
    _ = injectiveMoment H node58 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7186 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7186 = injectiveMoment H raw7186step0 := by
      have heq : raw7186step0 = raw7186.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7186).symm
    injectiveMoment H raw7186step0 = injectiveMoment H raw7186step1 := by
      have heq : raw7186step1 = (fun i j => raw7186step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7186step0 permutation25 permutation7
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical7333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7333 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7333 = injectiveMoment H raw7333step0 := by
      have heq : raw7333step0 = -raw7333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7333).symm
    injectiveMoment H raw7333step0 = injectiveMoment H raw7333step1 := by
      have hz : ∀ i, raw7333step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7333step1 = (fun i j => raw7333step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7333step0 permutation15 hz
    injectiveMoment H raw7333step1 = injectiveMoment H raw7333step2 := by
      have heq : raw7333step2 = (fun i j => raw7333step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7333step1 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7497 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7497 = injectiveMoment H raw7497step0 := by
      have heq : raw7497step0 = -raw7497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7497).symm
    injectiveMoment H raw7497step0 = injectiveMoment H raw7497step1 := by
      have hz : ∀ i, raw7497step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7497step1 = (fun i j => raw7497step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7497step0 permutation15 hz
    injectiveMoment H raw7497step1 = injectiveMoment H raw7497step2 := by
      have heq : raw7497step2 = (fun i j => raw7497step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7497step1 permutation8 permutation3
    _ = injectiveMoment H node58 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7815 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7815 = injectiveMoment H raw7815step0 := by
      have heq : raw7815step0 = raw7815.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7815).symm
    injectiveMoment H raw7815step0 = injectiveMoment H raw7815step1 := by
      have heq : raw7815step1 = (fun i j => raw7815step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7815step0 permutation24 permutation7
    _ = injectiveMoment H node272 := by rfl

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

theorem canonical7919 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7919 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw7919 = injectiveMoment H raw7919step0 := by
      have heq : raw7919step0 = raw7919.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7919).symm
    injectiveMoment H raw7919step0 = injectiveMoment H raw7919step1 := by
      have heq : raw7919step1 = -raw7919step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7919step0).symm
    injectiveMoment H raw7919step1 = injectiveMoment H raw7919step2 := by
      have heq : raw7919step2 = (fun i j => raw7919step1 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7919step1 permutation17 permutation4
    _ = injectiveMoment H node261 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7941 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw7941 = injectiveMoment H raw7941step0 := by
      have heq : raw7941step0 = raw7941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7941).symm
    injectiveMoment H raw7941step0 = injectiveMoment H raw7941step1 := by
      have heq : raw7941step1 = -raw7941step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7941step0).symm
    injectiveMoment H raw7941step1 = injectiveMoment H raw7941step2 := by
      have heq : raw7941step2 = (fun i j => raw7941step1 (permutation16 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7941step1 permutation16 permutation7
    _ = injectiveMoment H node176 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

theorem canonical814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw814 = injectiveMoment H node21 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8046 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8046 = injectiveMoment H raw8046step0 := by
      have hz : ∀ i, raw8046 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8046step0 = (fun i j => raw8046 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8046 permutation9 hz
    _ = injectiveMoment H node36 := by rfl

theorem canonical8047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8047 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw8047 = injectiveMoment H raw8047step0 := by
      have hz : ∀ i, raw8047 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8047step0 = (fun i j => raw8047 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8047 permutation9 hz
    _ = injectiveMoment H node37 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8156 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8156 = injectiveMoment H raw8156step0 := by
      have hz : ∀ i, raw8156 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8156step0 = (fun i j => raw8156 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8156 permutation9 hz
    _ = injectiveMoment H node43 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8296 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8296 = injectiveMoment H raw8296step0 := by
      have heq : raw8296step0 = -raw8296 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8296).symm
    injectiveMoment H raw8296step0 = injectiveMoment H raw8296step1 := by
      have hz : ∀ i, raw8296step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8296step1 = (fun i j => raw8296step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8296step0 permutation9 hz
    injectiveMoment H raw8296step1 = injectiveMoment H raw8296step2 := by
      have heq : raw8296step2 = (fun i j => raw8296step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8296step1 permutation8 permutation3
    _ = injectiveMoment H node43 := by rfl

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

theorem canonical840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw840 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw840 = injectiveMoment H raw840step0 := by
      have heq : raw840step0 = (fun i j => raw840 (permutation5 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw840 permutation5 permutation7
    _ = injectiveMoment H node43 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8817 = injectiveMoment H node1103 := by
  calc
    injectiveMoment H raw8817 = injectiveMoment H raw8817step0 := by
      have heq : raw8817step0 = raw8817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8817).symm
    injectiveMoment H raw8817step0 = injectiveMoment H raw8817step1 := by
      have heq : raw8817step1 = (fun i j => raw8817step0 (permutation19 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8817step0 permutation19 permutation14
    _ = injectiveMoment H node1103 := by rfl

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

theorem canonical8873 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8873 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw8873 = injectiveMoment H raw8873step0 := by
      have heq : raw8873step0 = raw8873.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8873).symm
    injectiveMoment H raw8873step0 = injectiveMoment H raw8873step1 := by
      have heq : raw8873step1 = (fun i j => raw8873step0 (permutation19 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8873step0 permutation19 permutation14
    _ = injectiveMoment H node1109 := by rfl

theorem canonical8875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8875 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw8875 = injectiveMoment H raw8875step0 := by
      have heq : raw8875step0 = -raw8875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8875).symm
    injectiveMoment H raw8875step0 = injectiveMoment H raw8875step1 := by
      have hz : ∀ i, raw8875step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8875step1 = (fun i j => raw8875step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8875step0 permutation9 hz
    injectiveMoment H raw8875step1 = injectiveMoment H raw8875step2 := by
      have heq : raw8875step2 = (fun i j => raw8875step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8875step1 permutation23 permutation3
    _ = injectiveMoment H node263 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
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

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2478 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2478 = injectiveMoment H node1018 := by
  calc
    injectiveMoment H raw2478 = injectiveMoment H raw2478step0 := by
      have heq : raw2478step0 = raw2478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2478).symm
    injectiveMoment H raw2478step0 = injectiveMoment H raw2478step1 := by
      have heq : raw2478step1 = -raw2478step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2478step0).symm
    injectiveMoment H raw2478step1 = injectiveMoment H raw2478step2 := by
      have heq : raw2478step2 = (fun i j => raw2478step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2478step1 permutation14 permutation26
    _ = injectiveMoment H node1018 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2864 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2864 = injectiveMoment H raw2864step0 := by
      have heq : raw2864step0 = raw2864.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2864).symm
    injectiveMoment H raw2864step0 = injectiveMoment H raw2864step1 := by
      have heq : raw2864step1 = (fun i j => raw2864step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2864step0 permutation6 permutation7
    _ = injectiveMoment H node63 := by rfl

theorem canonical2870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2870 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw2870 = injectiveMoment H raw2870step0 := by
      have heq : raw2870step0 = raw2870.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2870).symm
    injectiveMoment H raw2870step0 = injectiveMoment H raw2870step1 := by
      have heq : raw2870step1 = -raw2870step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2870step0).symm
    injectiveMoment H raw2870step1 = injectiveMoment H raw2870step2 := by
      have heq : raw2870step2 = (fun i j => raw2870step1 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2870step1 permutation26 permutation4
    _ = injectiveMoment H node107 := by rfl

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

theorem sound21 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node21 = Sparse.eval value21 (momentVector H) := by
  have hc : momentVector H 34 = injectiveMoment H node21 := rfl
  simp [value21, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound107 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node107 = Sparse.eval value107 (momentVector H) := by
  have heq : pivotMatrix107 = (fun u v => node107 (pivotPermutation107 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node107 = injectiveMoment H pivotMatrix107 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix107 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix107 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix107 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (0 : Fin 3) = raw582 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical582 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix107 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (1 : Fin 3) = raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical813 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix107 (2 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix107 (2 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node107 + (injectiveMoment H (mergeFirst pivotMatrix107 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix107 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix107 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value107, value21, value36, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node109 = Sparse.eval value109 (momentVector H) := by
  have heq : pivotMatrix109 = (fun u v => node109 (pivotPermutation109 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node109 = injectiveMoment H pivotMatrix109 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix109 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix109 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (0 : Fin 3) = raw840 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical840 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) =
      Sparse.eval value21 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (1 : Fin 3) = raw814 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical814 hH).trans (sound21 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix109 (2 : Fin 3) = raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical813 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node109 + (injectiveMoment H (mergeFirst pivotMatrix109 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix109 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value109, value21, value36, value43, Sparse.eval] at hc ⊢
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

theorem sound170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node170 = Sparse.eval value170 (momentVector H) := by
  have heq : pivotMatrix170 = (fun u v => node170 (pivotPermutation170 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node170 = injectiveMoment H pivotMatrix170 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix170 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix170 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix170 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (0 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix170 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix170 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix170 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node170 + (injectiveMoment H (mergeFirst pivotMatrix170 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix170 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix170 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value170, value32, value36, value37, Sparse.eval] at hc ⊢
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

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
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

theorem sound188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node188 = Sparse.eval value188 (momentVector H) := by
  have heq : pivotMatrix188 = (fun u v => node188 (pivotPermutation188 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node188 = injectiveMoment H pivotMatrix188 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix188 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix188 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (0 : Fin 3) = raw5982 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5982 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (1 : Fin 3) = raw2864 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2864 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix188 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node188 + (injectiveMoment H (mergeFirst pivotMatrix188 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix188 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value188, value37, value58, value63, Sparse.eval] at hc ⊢
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
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
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

theorem sound271 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node271 = Sparse.eval value271 (momentVector H) := by
  have heq : pivotMatrix271 = (fun u v => node271 (pivotPermutation271 u) v) := by apply Matrix.ext; unfold pivotMatrix271 node271 pivotPermutation271; decide +kernel
  have hmoment : injectiveMoment H node271 = injectiveMoment H pivotMatrix271 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix271 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix271 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix271 (2 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix271 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node271 + (injectiveMoment H (mergeFirst pivotMatrix271 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix271 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value271, value56, value57, value61, Sparse.eval] at hc ⊢
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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound12
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound807 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node807 = Sparse.eval value807 (momentVector H) := by
  have heq : pivotMatrix807 = (fun u v => node807 (pivotPermutation807 u) v) := by apply Matrix.ext; unfold pivotMatrix807 node807 pivotPermutation807; decide +kernel
  have hmoment : injectiveMoment H node807 = injectiveMoment H pivotMatrix807 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix807 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix807 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix807 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (0 : Fin 3) = raw8046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw8046; decide +kernel
    rw [heq]
    exact (canonical8046 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix807 (1 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (1 : Fin 3) = raw5729 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw5729; decide +kernel
    rw [heq]
    exact (canonical5729 hH).trans (sound185 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix807 (2 : Fin 3)) =
      Sparse.eval value177 (momentVector H) := by
    have heq : mergeFirst pivotMatrix807 (2 : Fin 3) = raw5695 := by apply Matrix.ext; unfold mergeFirst pivotMatrix807 raw5695; decide +kernel
    rw [heq]
    exact (canonical5695 hH).trans (sound177 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node807 + (injectiveMoment H (mergeFirst pivotMatrix807 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix807 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix807 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value807, value177, value185, value36, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node949 = Sparse.eval value949 (momentVector H) := by
  have heq : pivotMatrix949 = (fun u v => node949 (pivotPermutation949 u) v) := by apply Matrix.ext; unfold pivotMatrix949 node949 pivotPermutation949; decide +kernel
  have hmoment : injectiveMoment H node949 = injectiveMoment H pivotMatrix949 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix949 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix949 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix949 (0 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (0 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix949 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix949 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix949 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix949 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node949 + (injectiveMoment H (mergeFirst pivotMatrix949 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix949 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix949 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value949, value109, value176, value263, Sparse.eval] at hc ⊢
  linarith

theorem sound950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node950 = Sparse.eval value950 (momentVector H) := by
  have heq : pivotMatrix950 = (fun u v => node950 (pivotPermutation950 u) v) := by apply Matrix.ext; unfold pivotMatrix950 node950 pivotPermutation950; decide +kernel
  have hmoment : injectiveMoment H node950 = injectiveMoment H pivotMatrix950 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix950 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix950 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix950 (0 : Fin 3)) =
      Sparse.eval value185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (0 : Fin 3) = raw7186 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw7186; decide +kernel
    rw [heq]
    exact (canonical7186 hH).trans (sound185 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix950 (1 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (1 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix950 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix950 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix950 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node950 + (injectiveMoment H (mergeFirst pivotMatrix950 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix950 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix950 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value950, value109, value185, value188, Sparse.eval] at hc ⊢
  linarith

theorem sound952 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node952 = Sparse.eval value952 (momentVector H) := by
  have heq : pivotMatrix952 = (fun u v => node952 (pivotPermutation952 u) v) := by apply Matrix.ext; unfold pivotMatrix952 node952 pivotPermutation952; decide +kernel
  have hmoment : injectiveMoment H node952 = injectiveMoment H pivotMatrix952 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix952 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix952 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix952 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (0 : Fin 3) = raw8296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw8296; decide +kernel
    rw [heq]
    exact (canonical8296 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix952 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (1 : Fin 3) = raw6335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw6335; decide +kernel
    rw [heq]
    exact (canonical6335 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix952 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix952 (2 : Fin 3) = raw6232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix952 raw6232; decide +kernel
    rw [heq]
    exact (canonical6232 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node952 + (injectiveMoment H (mergeFirst pivotMatrix952 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix952 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix952 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value952, value109, value229, value43, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node974 = Sparse.eval value974 (momentVector H) := by
  have heq : pivotMatrix974 = (fun u v => node974 (pivotPermutation974 u) v) := by apply Matrix.ext; unfold pivotMatrix974 node974 pivotPermutation974; decide +kernel
  have hmoment : injectiveMoment H node974 = injectiveMoment H pivotMatrix974 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix974 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix974 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix974 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (0 : Fin 3) = raw7106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw7106; decide +kernel
    rw [heq]
    exact (canonical7106 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix974 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (1 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix974 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix974 (2 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix974 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node974 + (injectiveMoment H (mergeFirst pivotMatrix974 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix974 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix974 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value974, value176, value271, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound979 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node979 = Sparse.eval value979 (momentVector H) := by
  have heq : pivotMatrix979 = (fun u v => node979 (pivotPermutation979 u) v) := by apply Matrix.ext; unfold pivotMatrix979 node979 pivotPermutation979; decide +kernel
  have hmoment : injectiveMoment H node979 = injectiveMoment H pivotMatrix979 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix979 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix979 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix979 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (0 : Fin 3) = raw8047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw8047; decide +kernel
    rw [heq]
    exact (canonical8047 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix979 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (1 : Fin 3) = raw6336 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw6336; decide +kernel
    rw [heq]
    exact (canonical6336 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix979 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix979 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix979 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node979 + (injectiveMoment H (mergeFirst pivotMatrix979 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix979 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix979 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value979, value170, value188, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound1018 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1018 = Sparse.eval value1018 (momentVector H) := by
  have heq : pivotMatrix1018 = (fun u v => node1018.transpose (pivotPermutation1018 u) v) := by apply Matrix.ext; unfold pivotMatrix1018 node1018 pivotPermutation1018; decide +kernel
  have hmoment : injectiveMoment H node1018 = injectiveMoment H pivotMatrix1018 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1018 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1018 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1018 (0 : Fin 3)) =
      Sparse.eval value107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (0 : Fin 3) = raw2870 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw2870; decide +kernel
    rw [heq]
    exact (canonical2870 hH).trans (sound107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1018 (1 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (1 : Fin 3) = raw6961 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw6961; decide +kernel
    rw [heq]
    exact (canonical6961 hH).trans (sound109 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1018 (2 : Fin 3)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1018 (2 : Fin 3) = raw6969 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1018 raw6969; decide +kernel
    rw [heq]
    exact (canonical6969 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1018 + (injectiveMoment H (mergeFirst pivotMatrix1018 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1018 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1018 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1018, value107, value109, Sparse.eval] at hc ⊢
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

theorem sound1103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1103 = Sparse.eval value1103 (momentVector H) := by
  have heq : pivotMatrix1103 = (fun u v => node1103 (pivotPermutation1103 u) v) := by apply Matrix.ext; unfold pivotMatrix1103 node1103 pivotPermutation1103; decide +kernel
  have hmoment : injectiveMoment H node1103 = injectiveMoment H pivotMatrix1103 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1103 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1103 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1103 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (0 : Fin 3) = raw7497 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw7497; decide +kernel
    rw [heq]
    exact (canonical7497 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1103 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (1 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1103 (2 : Fin 3)) =
      Sparse.eval value248 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1103 (2 : Fin 3) = raw6630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1103 raw6630; decide +kernel
    rw [heq]
    exact (canonical6630 hH).trans (sound248 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1103 + (injectiveMoment H (mergeFirst pivotMatrix1103 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1103 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1103 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1103, value248, value263, value58, Sparse.eval] at hc ⊢
  linarith

theorem sound1109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1109 = Sparse.eval value1109 (momentVector H) := by
  have heq : pivotMatrix1109 = (fun u v => node1109 (pivotPermutation1109 u) v) := by apply Matrix.ext; unfold pivotMatrix1109 node1109 pivotPermutation1109; decide +kernel
  have hmoment : injectiveMoment H node1109 = injectiveMoment H pivotMatrix1109 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1109 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1109 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1109 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (0 : Fin 3) = raw7333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw7333; decide +kernel
    rw [heq]
    exact (canonical7333 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1109 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (1 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1109 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1109 (2 : Fin 3) = raw6640 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1109 raw6640; decide +kernel
    rw [heq]
    exact (canonical6640 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1109 + (injectiveMoment H (mergeFirst pivotMatrix1109 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1109 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1109 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1109, value176, value263, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound1123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1123 = Sparse.eval value1123 (momentVector H) := by
  have heq : pivotMatrix1123 = (fun u v => node1123.transpose (pivotPermutation1123 u) v) := by apply Matrix.ext; unfold pivotMatrix1123 node1123 pivotPermutation1123; decide +kernel
  have hmoment : injectiveMoment H node1123 = injectiveMoment H pivotMatrix1123 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1123 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1123 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1123 (0 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (0 : Fin 3) = raw5044 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw5044; decide +kernel
    rw [heq]
    exact (canonical5044 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1123 (1 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (1 : Fin 3) = raw7919 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw7919; decide +kernel
    rw [heq]
    exact (canonical7919 hH).trans (sound261 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1123 (2 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1123 (2 : Fin 3) = raw7941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1123 raw7941; decide +kernel
    rw [heq]
    exact (canonical7941 hH).trans (sound176 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1123 + (injectiveMoment H (mergeFirst pivotMatrix1123 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1123 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1123 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1123, value176, value229, value261, Sparse.eval] at hc ⊢
  linarith

theorem sound1124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1124 = Sparse.eval value1124 (momentVector H) := by
  have heq : pivotMatrix1124 = (fun u v => node1124 (pivotPermutation1124 u) v) := by apply Matrix.ext; unfold pivotMatrix1124 node1124 pivotPermutation1124; decide +kernel
  have hmoment : injectiveMoment H node1124 = injectiveMoment H pivotMatrix1124 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1124 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1124 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1124 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (0 : Fin 3) = raw8156 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw8156; decide +kernel
    rw [heq]
    exact (canonical8156 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1124 (1 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (1 : Fin 3) = raw6717 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw6717; decide +kernel
    rw [heq]
    exact (canonical6717 hH).trans (sound263 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1124 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1124 (2 : Fin 3) = raw6688 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1124 raw6688; decide +kernel
    rw [heq]
    exact (canonical6688 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1124 + (injectiveMoment H (mergeFirst pivotMatrix1124 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1124 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1124 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1124, value263, value43, Sparse.eval] at hc ⊢
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

theorem sound1212 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1212 = Sparse.eval value1212 (momentVector H) := by
  have heq : pivotMatrix1212 = (fun u v => node1212 (pivotPermutation1212 u) v) := by apply Matrix.ext; unfold pivotMatrix1212 node1212 pivotPermutation1212; decide +kernel
  have hmoment : injectiveMoment H node1212 = injectiveMoment H pivotMatrix1212 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1212 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1212 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1212 (0 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (0 : Fin 3) = raw7815 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7815; decide +kernel
    rw [heq]
    exact (canonical7815 hH).trans (sound272 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1212 (1 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (1 : Fin 3) = raw7108 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7108; decide +kernel
    rw [heq]
    exact (canonical7108 hH).trans (sound58 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1212 (2 : Fin 3)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1212 (2 : Fin 3) = raw7089 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1212 raw7089; decide +kernel
    rw [heq]
    exact (canonical7089 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1212 + (injectiveMoment H (mergeFirst pivotMatrix1212 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1212 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1212 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1212, value263, value272, value58, Sparse.eval] at hc ⊢
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

theorem sound590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node590 = Sparse.eval value590 (momentVector H) := by
  have hc : momentVector H 139 = injectiveMoment H node590 := rfl
  simp [value590, Sparse.eval, hc]

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

theorem sound2020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2020 = Sparse.eval value2020 (momentVector H) := by
  have heq : pivotMatrix2020 = (fun u v => node2020 (pivotPermutation2020 u) v) := by apply Matrix.ext; unfold pivotMatrix2020 node2020 pivotPermutation2020; decide +kernel
  have hmoment : injectiveMoment H node2020 = injectiveMoment H pivotMatrix2020 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2020 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2020 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2020 (0 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (0 : Fin 4) = raw2478 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw2478; decide +kernel
    rw [heq]
    exact (canonical2478 hH).trans (sound1018 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2020 (1 : Fin 4)) =
      Sparse.eval value979 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (1 : Fin 4) = raw3509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3509; decide +kernel
    rw [heq]
    exact (canonical3509 hH).trans (sound979 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2020 (2 : Fin 4)) =
      Sparse.eval value590 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (2 : Fin 4) = raw3600 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3600; decide +kernel
    rw [heq]
    exact (canonical3600 hH).trans (sound590 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2020 (3 : Fin 4)) =
      Sparse.eval value807 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2020 (3 : Fin 4) = raw3602 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2020 raw3602; decide +kernel
    rw [heq]
    exact (canonical3602 hH).trans (sound807 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2020 + (injectiveMoment H (mergeFirst pivotMatrix2020 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2020 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2020, value1018, value590, value807, value979, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound39
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2517 = Sparse.eval value2517 (momentVector H) := by
  have heq : pivotMatrix2517 = (fun u v => node2517 (pivotPermutation2517 u) v) := by apply Matrix.ext; unfold pivotMatrix2517 node2517 pivotPermutation2517; decide +kernel
  have hmoment : injectiveMoment H node2517 = injectiveMoment H pivotMatrix2517 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2517 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2517 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2517 (0 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (0 : Fin 4) = raw7051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw7051; decide +kernel
    rw [heq]
    exact (canonical7051 hH).trans (sound1124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2517 (1 : Fin 4)) =
      Sparse.eval value1123 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (1 : Fin 4) = raw6190 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6190; decide +kernel
    rw [heq]
    exact (canonical6190 hH).trans (sound1123 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2517 (2 : Fin 4)) =
      Sparse.eval value949 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (2 : Fin 4) = raw6159 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6159; decide +kernel
    rw [heq]
    exact (canonical6159 hH).trans (sound949 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2517 (3 : Fin 4)) =
      Sparse.eval value1018 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2517 (3 : Fin 4) = raw6157 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2517 raw6157; decide +kernel
    rw [heq]
    exact (canonical6157 hH).trans (sound1018 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2517 + (injectiveMoment H (mergeFirst pivotMatrix2517 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2517 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2517, value1018, value1123, value1124, value949, Sparse.eval] at hc ⊢
  linarith

theorem sound2545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2545 = Sparse.eval value2545 (momentVector H) := by
  have heq : pivotMatrix2545 = (fun u v => node2545 (pivotPermutation2545 u) v) := by apply Matrix.ext; unfold pivotMatrix2545 node2545 pivotPermutation2545; decide +kernel
  have hmoment : injectiveMoment H node2545 = injectiveMoment H pivotMatrix2545 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2545 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2545 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2545 (0 : Fin 4)) =
      Sparse.eval value1212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (0 : Fin 4) = raw7087 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw7087; decide +kernel
    rw [heq]
    exact (canonical7087 hH).trans (sound1212 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2545 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (1 : Fin 4) = raw6288 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6288; decide +kernel
    rw [heq]
    exact (canonical6288 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2545 (2 : Fin 4)) =
      Sparse.eval value952 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (2 : Fin 4) = raw6230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6230; decide +kernel
    rw [heq]
    exact (canonical6230 hH).trans (sound952 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2545 (3 : Fin 4)) =
      Sparse.eval value950 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2545 (3 : Fin 4) = raw6228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2545 raw6228; decide +kernel
    rw [heq]
    exact (canonical6228 hH).trans (sound950 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2545 + (injectiveMoment H (mergeFirst pivotMatrix2545 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2545 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2545, value1212, value950, value952, value974, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2773 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2773 = Sparse.eval value2773 (momentVector H) := by
  have heq : pivotMatrix2773 = (fun u v => node2773 (pivotPermutation2773 u) v) := by apply Matrix.ext; unfold pivotMatrix2773 node2773 pivotPermutation2773; decide +kernel
  have hmoment : injectiveMoment H node2773 = injectiveMoment H pivotMatrix2773 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2773 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2773 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2773 (0 : Fin 4)) =
      Sparse.eval value1124 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2773 (0 : Fin 4) = raw6687 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2773 raw6687; decide +kernel
    rw [heq]
    exact (canonical6687 hH).trans (sound1124 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2773 (1 : Fin 4)) =
      Sparse.eval value1103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2773 (1 : Fin 4) = raw8817 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2773 raw8817; decide +kernel
    rw [heq]
    exact (canonical8817 hH).trans (sound1103 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2773 (2 : Fin 4)) =
      Sparse.eval value1109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2773 (2 : Fin 4) = raw8873 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2773 raw8873; decide +kernel
    rw [heq]
    exact (canonical8873 hH).trans (sound1109 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2773 (3 : Fin 4)) =
      Sparse.eval value263 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2773 (3 : Fin 4) = raw8875 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2773 raw8875; decide +kernel
    rw [heq]
    exact (canonical8875 hH).trans (sound263 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2773 + (injectiveMoment H (mergeFirst pivotMatrix2773 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2773 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2773 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2773 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2773, value1103, value1109, value1124, value263, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound52
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3362_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3362 = Sparse.eval value3362 (momentVector H) := by
  have heq : pivotMatrix3362 = (fun u v => node3362 (pivotPermutation3362 u) v) := by apply Matrix.ext; unfold pivotMatrix3362 node3362 pivotPermutation3362; decide +kernel
  have hmoment : injectiveMoment H node3362 = injectiveMoment H pivotMatrix3362 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3362 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3362 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3362 (0 : Fin 5)) =
      Sparse.eval value2773 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3362 (0 : Fin 5) = raw7048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3362 raw7048; decide +kernel
    rw [heq]
    exact (canonical7048 hH).trans (sound2773 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3362 (1 : Fin 5)) =
      Sparse.eval value1768 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3362 (1 : Fin 5) = raw6187 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3362 raw6187; decide +kernel
    rw [heq]
    exact (canonical6187 hH).trans (sound1768_e hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3362 (2 : Fin 5)) =
      Sparse.eval value2020 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3362 (2 : Fin 5) = raw6153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3362 raw6153; decide +kernel
    rw [heq]
    exact (canonical6153 hH).trans (sound2020 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3362 (3 : Fin 5)) =
      Sparse.eval value2545 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3362 (3 : Fin 5) = raw6148 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3362 raw6148; decide +kernel
    rw [heq]
    exact (canonical6148 hH).trans (sound2545 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3362 (4 : Fin 5)) =
      Sparse.eval value2517 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3362 (4 : Fin 5) = raw6147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3362 raw6147; decide +kernel
    rw [heq]
    exact (canonical6147 hH).trans (sound2517 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3362 + (injectiveMoment H (mergeFirst pivotMatrix3362 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3362 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3362 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3362 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3362 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3362, value1768, value2020, value2517, value2545, value2773, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3362_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3362_e_oai
