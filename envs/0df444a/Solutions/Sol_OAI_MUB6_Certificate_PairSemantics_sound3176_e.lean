-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3176_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T07:07:26.593945+00:00
-- url     : https://prove2.me/submissions/4c96faec-e598-4455-8a13-55b4457a6e75

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3432 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3432 = injectiveMoment H node2028 := by
  rfl

theorem canonical3433 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3433 = injectiveMoment H node2762 := by
  calc
    injectiveMoment H raw3433 = injectiveMoment H raw3433step0 := by
      have heq : raw3433step0 = -raw3433 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3433).symm
    injectiveMoment H raw3433step0 = injectiveMoment H raw3433step1 := by
      have heq : raw3433step1 = (fun i j => raw3433step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3433step0 permutation100 permutation15
    _ = injectiveMoment H node2762 := by rfl

theorem canonical3440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3440 = injectiveMoment H node2029 := by
  rfl

theorem canonical3441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3441 = injectiveMoment H node406 := by
  calc
    injectiveMoment H raw3441 = injectiveMoment H raw3441step0 := by
      have heq : raw3441step0 = raw3441.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3441).symm
    injectiveMoment H raw3441step0 = injectiveMoment H raw3441step1 := by
      have heq : raw3441step1 = -raw3441step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3441step0).symm
    injectiveMoment H raw3441step1 = injectiveMoment H raw3441step2 := by
      have heq : raw3441step2 = (fun i j => raw3441step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3441step1 permutation29 permutation15
    _ = injectiveMoment H node406 := by rfl

theorem canonical3446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3446 = injectiveMoment H node411 := by
  calc
    injectiveMoment H raw3446 = injectiveMoment H raw3446step0 := by
      have heq : raw3446step0 = raw3446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3446).symm
    injectiveMoment H raw3446step0 = injectiveMoment H raw3446step1 := by
      have heq : raw3446step1 = -raw3446step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3446step0).symm
    injectiveMoment H raw3446step1 = injectiveMoment H raw3446step2 := by
      have heq : raw3446step2 = (fun i j => raw3446step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3446step1 permutation29 permutation16
    _ = injectiveMoment H node411 := by rfl

theorem canonical3450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3450 = injectiveMoment H node1120 := by
  calc
    injectiveMoment H raw3450 = injectiveMoment H raw3450step0 := by
      have heq : raw3450step0 = -raw3450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3450).symm
    injectiveMoment H raw3450step0 = injectiveMoment H raw3450step1 := by
      have heq : raw3450step1 = (fun i j => raw3450step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3450step0 permutation29 permutation15
    _ = injectiveMoment H node1120 := by rfl

theorem canonical3451 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3451 = injectiveMoment H node411 := by
  calc
    injectiveMoment H raw3451 = injectiveMoment H raw3451step0 := by
      have heq : raw3451step0 = raw3451.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3451).symm
    injectiveMoment H raw3451step0 = injectiveMoment H raw3451step1 := by
      have heq : raw3451step1 = -raw3451step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3451step0).symm
    injectiveMoment H raw3451step1 = injectiveMoment H raw3451step2 := by
      have heq : raw3451step2 = (fun i j => raw3451step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3451step1 permutation29 permutation15
    _ = injectiveMoment H node411 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical3510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3510 = injectiveMoment H node2037 := by
  rfl

theorem canonical3516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3516 = injectiveMoment H node611 := by
  rfl

theorem canonical3519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3519 = injectiveMoment H node1320 := by
  calc
    injectiveMoment H raw3519 = injectiveMoment H raw3519step0 := by
      have heq : raw3519step0 = -raw3519 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3519).symm
    injectiveMoment H raw3519step0 = injectiveMoment H raw3519step1 := by
      have heq : raw3519step1 = (fun i j => raw3519step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3519step0 permutation19 permutation15
    _ = injectiveMoment H node1320 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3541 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3541 = injectiveMoment H node488 := by
  calc
    injectiveMoment H raw3541 = injectiveMoment H raw3541step0 := by
      have heq : raw3541step0 = raw3541.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3541).symm
    injectiveMoment H raw3541step0 = injectiveMoment H raw3541step1 := by
      have heq : raw3541step1 = (fun i j => raw3541step0 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3541step0 permutation22 permutation19
    _ = injectiveMoment H node488 := by rfl

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

theorem canonical3614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3614 = injectiveMoment H node1376 := by
  calc
    injectiveMoment H raw3614 = injectiveMoment H raw3614step0 := by
      have heq : raw3614step0 = raw3614.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3614).symm
    injectiveMoment H raw3614step0 = injectiveMoment H raw3614step1 := by
      have heq : raw3614step1 = -raw3614step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3614step0).symm
    injectiveMoment H raw3614step1 = injectiveMoment H raw3614step2 := by
      have heq : raw3614step2 = (fun i j => raw3614step1 (permutation9 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3614step1 permutation9 permutation27
    _ = injectiveMoment H node1376 := by rfl

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

theorem canonical3641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3641 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw3641 = injectiveMoment H raw3641step0 := by
      have heq : raw3641step0 = raw3641.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3641).symm
    injectiveMoment H raw3641step0 = injectiveMoment H raw3641step1 := by
      have heq : raw3641step1 = (fun i j => raw3641step0 (permutation24 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3641step0 permutation24 permutation17
    _ = injectiveMoment H node496 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4197 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4197 = injectiveMoment H raw4197step0 := by
      have heq : raw4197step0 = raw4197.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4197).symm
    injectiveMoment H raw4197step0 = injectiveMoment H raw4197step1 := by
      have heq : raw4197step1 = (fun i j => raw4197step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4197step0 permutation13 permutation3
    _ = injectiveMoment H node197 := by rfl

theorem canonical4211 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4211 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw4211 = injectiveMoment H raw4211step0 := by
      have heq : raw4211step0 = raw4211.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4211).symm
    injectiveMoment H raw4211step0 = injectiveMoment H raw4211step1 := by
      have heq : raw4211step1 = -raw4211step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4211step0).symm
    injectiveMoment H raw4211step1 = injectiveMoment H raw4211step2 := by
      have heq : raw4211step2 = (fun i j => raw4211step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4211step1 permutation24 permutation3
    _ = injectiveMoment H node198 := by rfl

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

theorem canonical4493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4493 = injectiveMoment H node2216 := by
  rfl

theorem canonical4501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4501 = injectiveMoment H node593 := by
  calc
    injectiveMoment H raw4501 = injectiveMoment H raw4501step0 := by
      have heq : raw4501step0 = raw4501.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4501).symm
    injectiveMoment H raw4501step0 = injectiveMoment H raw4501step1 := by
      have heq : raw4501step1 = (fun i j => raw4501step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4501step0 permutation21 permutation19
    _ = injectiveMoment H node593 := by rfl

theorem canonical4504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4504 = injectiveMoment H node1317 := by
  calc
    injectiveMoment H raw4504 = injectiveMoment H raw4504step0 := by
      have heq : raw4504step0 = raw4504.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4504).symm
    injectiveMoment H raw4504step0 = injectiveMoment H raw4504step1 := by
      have heq : raw4504step1 = -raw4504step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4504step0).symm
    injectiveMoment H raw4504step1 = injectiveMoment H raw4504step2 := by
      have heq : raw4504step2 = (fun i j => raw4504step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4504step1 permutation9 permutation29
    _ = injectiveMoment H node1317 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4609 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw4609 = injectiveMoment H raw4609step0 := by
      have heq : raw4609step0 = raw4609.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4609).symm
    injectiveMoment H raw4609step0 = injectiveMoment H raw4609step1 := by
      have heq : raw4609step1 = -raw4609step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4609step0).symm
    injectiveMoment H raw4609step1 = injectiveMoment H raw4609step2 := by
      have heq : raw4609step2 = (fun i j => raw4609step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4609step1 permutation9 permutation29
    _ = injectiveMoment H node1310 := by rfl

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

theorem canonical4745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4745 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw4745 = injectiveMoment H raw4745step0 := by
      have heq : raw4745step0 = raw4745.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4745).symm
    injectiveMoment H raw4745step0 = injectiveMoment H raw4745step1 := by
      have heq : raw4745step1 = (fun i j => raw4745step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4745step0 permutation21 permutation19
    _ = injectiveMoment H node484 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4832 = injectiveMoment H node1369 := by
  calc
    injectiveMoment H raw4832 = injectiveMoment H raw4832step0 := by
      have heq : raw4832step0 = raw4832.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4832).symm
    injectiveMoment H raw4832step0 = injectiveMoment H raw4832step1 := by
      have heq : raw4832step1 = (fun i j => raw4832step0 (permutation32 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4832step0 permutation32 permutation27
    _ = injectiveMoment H node1369 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5329 = injectiveMoment H node1315 := by
  calc
    injectiveMoment H raw5329 = injectiveMoment H raw5329step0 := by
      have heq : raw5329step0 = raw5329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5329).symm
    injectiveMoment H raw5329step0 = injectiveMoment H raw5329step1 := by
      have heq : raw5329step1 = -raw5329step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5329step0).symm
    injectiveMoment H raw5329step1 = injectiveMoment H raw5329step2 := by
      have heq : raw5329step2 = (fun i j => raw5329step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5329step1 permutation9 permutation29
    _ = injectiveMoment H node1315 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5741 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5741 = injectiveMoment H raw5741step0 := by
      have heq : raw5741step0 = raw5741.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5741).symm
    injectiveMoment H raw5741step0 = injectiveMoment H raw5741step1 := by
      have heq : raw5741step1 = -raw5741step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5741step0).symm
    injectiveMoment H raw5741step1 = injectiveMoment H raw5741step2 := by
      have heq : raw5741step2 = (fun i j => raw5741step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5741step1 permutation27 permutation5
    _ = injectiveMoment H node146 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5803 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw5803 = injectiveMoment H raw5803step0 := by
      have heq : raw5803step0 = raw5803.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5803).symm
    injectiveMoment H raw5803step0 = injectiveMoment H raw5803step1 := by
      have heq : raw5803step1 = (fun i j => raw5803step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5803step0 permutation23 permutation5
    _ = injectiveMoment H node226 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6509 = injectiveMoment H node1059 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6935 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw6935 = injectiveMoment H raw6935step0 := by
      have heq : raw6935step0 = raw6935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6935).symm
    injectiveMoment H raw6935step0 = injectiveMoment H raw6935step1 := by
      have heq : raw6935step1 = (fun i j => raw6935step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6935step0 permutation28 permutation5
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical6950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6950 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6950 = injectiveMoment H raw6950step0 := by
      have heq : raw6950step0 = raw6950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6950).symm
    injectiveMoment H raw6950step0 = injectiveMoment H raw6950step1 := by
      have heq : raw6950step1 = -raw6950step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6950step0).symm
    injectiveMoment H raw6950step1 = injectiveMoment H raw6950step2 := by
      have heq : raw6950step2 = (fun i j => raw6950step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6950step1 permutation25 permutation3
    _ = injectiveMoment H node184 := by rfl

theorem canonical6968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6968 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6968 = injectiveMoment H raw6968step0 := by
      have heq : raw6968step0 = raw6968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6968).symm
    injectiveMoment H raw6968step0 = injectiveMoment H raw6968step1 := by
      have heq : raw6968step1 = (fun i j => raw6968step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6968step0 permutation28 permutation5
    _ = injectiveMoment H node170 := by rfl

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

theorem canonical7332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7332 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw7332 = injectiveMoment H raw7332step0 := by
      have heq : raw7332step0 = raw7332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7332).symm
    injectiveMoment H raw7332step0 = injectiveMoment H raw7332step1 := by
      have heq : raw7332step1 = -raw7332step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7332step0).symm
    injectiveMoment H raw7332step1 = injectiveMoment H raw7332step2 := by
      have heq : raw7332step2 = (fun i j => raw7332step1 (permutation30 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7332step1 permutation30 permutation9
    _ = injectiveMoment H node832 := by rfl

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

theorem canonical7511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7511 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw7511 = injectiveMoment H raw7511step0 := by
      have heq : raw7511step0 = raw7511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7511).symm
    injectiveMoment H raw7511step0 = injectiveMoment H raw7511step1 := by
      have heq : raw7511step1 = (fun i j => raw7511step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7511step0 permutation13 permutation3
    _ = injectiveMoment H node291 := by rfl

theorem canonical7512 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7512 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7512 = injectiveMoment H raw7512step0 := by
      have heq : raw7512step0 = raw7512.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7512).symm
    injectiveMoment H raw7512step0 = injectiveMoment H raw7512step1 := by
      have heq : raw7512step1 = -raw7512step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7512step0).symm
    injectiveMoment H raw7512step1 = injectiveMoment H raw7512step2 := by
      have heq : raw7512step2 = (fun i j => raw7512step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7512step1 permutation24 permutation3
    _ = injectiveMoment H node280 := by rfl

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

theorem canonical7539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7539 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw7539 = injectiveMoment H raw7539step0 := by
      have heq : raw7539step0 = raw7539.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7539).symm
    injectiveMoment H raw7539step0 = injectiveMoment H raw7539step1 := by
      have heq : raw7539step1 = -raw7539step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7539step0).symm
    injectiveMoment H raw7539step1 = injectiveMoment H raw7539step2 := by
      have heq : raw7539step2 = (fun i j => raw7539step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7539step1 permutation23 permutation3
    _ = injectiveMoment H node202 := by rfl

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

theorem canonical7585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7585 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7585 = injectiveMoment H raw7585step0 := by
      have heq : raw7585step0 = raw7585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7585).symm
    injectiveMoment H raw7585step0 = injectiveMoment H raw7585step1 := by
      have heq : raw7585step1 = (fun i j => raw7585step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7585step0 permutation28 permutation5
    _ = injectiveMoment H node284 := by rfl

theorem canonical7590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7590 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7590 = injectiveMoment H raw7590step0 := by
      have heq : raw7590step0 = raw7590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7590).symm
    injectiveMoment H raw7590step0 = injectiveMoment H raw7590step1 := by
      have heq : raw7590step1 = -raw7590step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7590step0).symm
    injectiveMoment H raw7590step1 = injectiveMoment H raw7590step2 := by
      have heq : raw7590step2 = (fun i j => raw7590step1 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7590step1 permutation15 permutation5
    _ = injectiveMoment H node210 := by rfl

theorem canonical7591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7591 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7591 = injectiveMoment H raw7591step0 := by
      have heq : raw7591step0 = raw7591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7591).symm
    injectiveMoment H raw7591step0 = injectiveMoment H raw7591step1 := by
      have heq : raw7591step1 = (fun i j => raw7591step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7591step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

theorem canonical7592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7592 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw7592 = injectiveMoment H raw7592step0 := by
      have heq : raw7592step0 = raw7592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7592).symm
    injectiveMoment H raw7592step0 = injectiveMoment H raw7592step1 := by
      have heq : raw7592step1 = -raw7592step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7592step0).symm
    injectiveMoment H raw7592step1 = injectiveMoment H raw7592step2 := by
      have heq : raw7592step2 = (fun i j => raw7592step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7592step1 permutation23 permutation3
    _ = injectiveMoment H node166 := by rfl

theorem canonical7603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7603 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7603 = injectiveMoment H raw7603step0 := by
      have heq : raw7603step0 = raw7603.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7603).symm
    injectiveMoment H raw7603step0 = injectiveMoment H raw7603step1 := by
      have heq : raw7603step1 = -raw7603step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7603step0).symm
    injectiveMoment H raw7603step1 = injectiveMoment H raw7603step2 := by
      have heq : raw7603step2 = (fun i j => raw7603step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7603step1 permutation23 permutation3
    _ = injectiveMoment H node201 := by rfl

theorem canonical7606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7606 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7606 = injectiveMoment H raw7606step0 := by
      have heq : raw7606step0 = raw7606.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7606).symm
    injectiveMoment H raw7606step0 = injectiveMoment H raw7606step1 := by
      have heq : raw7606step1 = -raw7606step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7606step0).symm
    injectiveMoment H raw7606step1 = injectiveMoment H raw7606step2 := by
      have heq : raw7606step2 = (fun i j => raw7606step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7606step1 permutation23 permutation3
    _ = injectiveMoment H node184 := by rfl

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

theorem canonical7616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7616 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw7616 = injectiveMoment H raw7616step0 := by
      have heq : raw7616step0 = raw7616.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7616).symm
    injectiveMoment H raw7616step0 = injectiveMoment H raw7616step1 := by
      have heq : raw7616step1 = (fun i j => raw7616step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7616step0 permutation28 permutation5
    _ = injectiveMoment H node269 := by rfl

theorem canonical7617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7617 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw7617 = injectiveMoment H raw7617step0 := by
      have heq : raw7617step0 = raw7617.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7617).symm
    injectiveMoment H raw7617step0 = injectiveMoment H raw7617step1 := by
      have heq : raw7617step1 = (fun i j => raw7617step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7617step0 permutation28 permutation5
    _ = injectiveMoment H node141 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8120 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8120 = injectiveMoment H raw8120step0 := by
      have heq : raw8120step0 = -raw8120 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8120).symm
    injectiveMoment H raw8120step0 = injectiveMoment H raw8120step1 := by
      have hz : ∀ i, raw8120step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8120step1 = (fun i j => raw8120step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8120step0 permutation9 hz
    injectiveMoment H raw8120step1 = injectiveMoment H raw8120step2 := by
      have heq : raw8120step2 = (fun i j => raw8120step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8120step1 permutation8 permutation3
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8368 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw8368 = injectiveMoment H raw8368step0 := by
      have heq : raw8368step0 = (fun i j => raw8368 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8368 permutation15 permutation9
    _ = injectiveMoment H node1311 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8489 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw8489 = injectiveMoment H raw8489step0 := by
      have heq : raw8489step0 = (fun i j => raw8489 (permutation21 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8489 permutation21 permutation11
    _ = injectiveMoment H node1316 := by rfl

theorem canonical8498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8498 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8498 = injectiveMoment H raw8498step0 := by
      have hz : ∀ i, raw8498 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8498step0 = (fun i j => raw8498 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8498 permutation9 hz
    injectiveMoment H raw8498step0 = injectiveMoment H raw8498step1 := by
      have heq : raw8498step1 = (fun i j => raw8498step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8498step0 permutation28 permutation5
    _ = injectiveMoment H node169 := by rfl

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

theorem canonical8928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8928 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw8928 = injectiveMoment H raw8928step0 := by
      have heq : raw8928step0 = raw8928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8928).symm
    injectiveMoment H raw8928step0 = injectiveMoment H raw8928step1 := by
      have heq : raw8928step1 = -raw8928step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8928step0).symm
    injectiveMoment H raw8928step1 = injectiveMoment H raw8928step2 := by
      have heq : raw8928step2 = (fun i j => raw8928step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8928step1 permutation21 permutation3
    _ = injectiveMoment H node175 := by rfl

theorem canonical8934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8934 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw8934 = injectiveMoment H raw8934step0 := by
      have heq : raw8934step0 = raw8934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8934).symm
    injectiveMoment H raw8934step0 = injectiveMoment H raw8934step1 := by
      have heq : raw8934step1 = -raw8934step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8934step0).symm
    injectiveMoment H raw8934step1 = injectiveMoment H raw8934step2 := by
      have heq : raw8934step2 = (fun i j => raw8934step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8934step1 permutation21 permutation3
    _ = injectiveMoment H node167 := by rfl

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

theorem canonical958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw958 = injectiveMoment H node28 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9950 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9950 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw9950 = injectiveMoment H raw9950step0 := by
      have heq : raw9950step0 = raw9950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9950).symm
    injectiveMoment H raw9950step0 = injectiveMoment H raw9950step1 := by
      have heq : raw9950step1 = -raw9950step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9950step0).symm
    injectiveMoment H raw9950step1 = injectiveMoment H raw9950step2 := by
      have heq : raw9950step2 = (fun i j => raw9950step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9950step1 permutation21 permutation3
    _ = injectiveMoment H node280 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9987 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw9987 = injectiveMoment H raw9987step0 := by
      have heq : raw9987step0 = raw9987.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9987).symm
    injectiveMoment H raw9987step0 = injectiveMoment H raw9987step1 := by
      have heq : raw9987step1 = -raw9987step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9987step0).symm
    injectiveMoment H raw9987step1 = injectiveMoment H raw9987step2 := by
      have heq : raw9987step2 = (fun i j => raw9987step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9987step1 permutation21 permutation3
    _ = injectiveMoment H node169 := by rfl

theorem canonical9991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9991 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw9991 = injectiveMoment H raw9991step0 := by
      have heq : raw9991step0 = raw9991.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9991).symm
    injectiveMoment H raw9991step0 = injectiveMoment H raw9991step1 := by
      have heq : raw9991step1 = (fun i j => raw9991step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9991step0 permutation29 permutation3
    _ = injectiveMoment H node162 := by rfl

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

theorem canonical10143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10143 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw10143 = injectiveMoment H raw10143step0 := by
      have heq : raw10143step0 = raw10143.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10143).symm
    injectiveMoment H raw10143step0 = injectiveMoment H raw10143step1 := by
      have heq : raw10143step1 = (fun i j => raw10143step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10143step0 permutation30 permutation3
    _ = injectiveMoment H node280 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10168 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw10168 = injectiveMoment H raw10168step0 := by
      have heq : raw10168step0 = raw10168.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10168).symm
    injectiveMoment H raw10168step0 = injectiveMoment H raw10168step1 := by
      have heq : raw10168step1 = (fun i j => raw10168step0 (permutation29 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10168step0 permutation29 permutation3
    _ = injectiveMoment H node223 := by rfl

theorem canonical10172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10172 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw10172 = injectiveMoment H raw10172step0 := by
      have heq : raw10172step0 = raw10172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10172).symm
    injectiveMoment H raw10172step0 = injectiveMoment H raw10172step1 := by
      have heq : raw10172step1 = (fun i j => raw10172step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10172step0 permutation30 permutation3
    _ = injectiveMoment H node196 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10180 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw10180 = injectiveMoment H raw10180step0 := by
      have heq : raw10180step0 = raw10180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10180).symm
    injectiveMoment H raw10180step0 = injectiveMoment H raw10180step1 := by
      have heq : raw10180step1 = (fun i j => raw10180step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10180step0 permutation30 permutation3
    _ = injectiveMoment H node198 := by rfl

theorem canonical10183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10183 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw10183 = injectiveMoment H raw10183step0 := by
      have heq : raw10183step0 = raw10183.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10183).symm
    injectiveMoment H raw10183step0 = injectiveMoment H raw10183step1 := by
      have heq : raw10183step1 = (fun i j => raw10183step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10183step0 permutation30 permutation3
    _ = injectiveMoment H node163 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2729 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw2729 = injectiveMoment H raw2729step0 := by
      have heq : raw2729step0 = -raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2729).symm
    injectiveMoment H raw2729step0 = injectiveMoment H raw2729step1 := by
      have heq : raw2729step1 = (fun i j => raw2729step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2729step0 permutation8 permutation3
    _ = injectiveMoment H node27 := by rfl

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

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

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

theorem sound27 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node27 = Sparse.eval value27 (momentVector H) := by
  have hc : momentVector H 69 = injectiveMoment H node27 := rfl
  simp [value27, Sparse.eval, hc]

theorem sound28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node28 = Sparse.eval value28 (momentVector H) := by
  have hc : momentVector H 70 = injectiveMoment H node28 := rfl
  simp [value28, Sparse.eval, hc]

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

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

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

theorem sound141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node141 = Sparse.eval value141 (momentVector H) := by
  have heq : pivotMatrix141 = (fun u v => node141 (pivotPermutation141 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node141 = injectiveMoment H pivotMatrix141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix141 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix141 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (0 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node141 + (injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value141, value28, value31, value32, Sparse.eval] at hc ⊢
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

theorem sound162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node162 = Sparse.eval value162 (momentVector H) := by
  have hc : momentVector H 124 = injectiveMoment H node162 := rfl
  simp [value162, Sparse.eval, hc]

theorem sound163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node163 = Sparse.eval value163 (momentVector H) := by
  have hc : momentVector H 125 = injectiveMoment H node163 := rfl
  simp [value163, Sparse.eval, hc]

theorem sound166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node166 = Sparse.eval value166 (momentVector H) := by
  have heq : pivotMatrix166 = (fun u v => node166 (pivotPermutation166 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node166 = injectiveMoment H pivotMatrix166 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix166 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix166 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3)) =
      Sparse.eval value27 (momentVector H) := by
    have heq : mergeFirst pivotMatrix166 (2 : Fin 3) = raw2729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2729 hH).trans (sound27 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node166 + (injectiveMoment H (mergeFirst pivotMatrix166 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix166 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value166, value27, value40, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node167 = Sparse.eval value167 (momentVector H) := by
  have hc : momentVector H 126 = injectiveMoment H node167 := rfl
  simp [value167, Sparse.eval, hc]

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

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

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

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

theorem sound196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node196 = Sparse.eval value196 (momentVector H) := by
  have hc : momentVector H 197 = injectiveMoment H node196 := rfl
  simp [value196, Sparse.eval, hc]

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node201 = Sparse.eval value201 (momentVector H) := by
  have heq : pivotMatrix201 = (fun u v => node201 (pivotPermutation201 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node201 = injectiveMoment H pivotMatrix201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix201 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix201 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (2 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node201 + (injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value201, value31, value32, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node202 = Sparse.eval value202 (momentVector H) := by
  have hc : momentVector H 24 = injectiveMoment H node202 := rfl
  simp [value202, Sparse.eval, hc]

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem sound223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node223 = Sparse.eval value223 (momentVector H) := by
  have hc : momentVector H 56 = injectiveMoment H node223 := rfl
  simp [value223, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound13
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound832 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node832 = Sparse.eval value832 (momentVector H) := by
  have heq : pivotMatrix832 = (fun u v => node832 (pivotPermutation832 u) v) := by apply Matrix.ext; unfold pivotMatrix832 node832 pivotPermutation832; decide +kernel
  have hmoment : injectiveMoment H node832 = injectiveMoment H pivotMatrix832 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix832 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix832 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix832 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (0 : Fin 3) = raw8120 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw8120; decide +kernel
    rw [heq]
    exact (canonical8120 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix832 (1 : Fin 3)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (1 : Fin 3) = raw5803 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw5803; decide +kernel
    rw [heq]
    exact (canonical5803 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix832 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix832 (2 : Fin 3) = raw5741 := by apply Matrix.ext; unfold mergeFirst pivotMatrix832 raw5741; decide +kernel
    rw [heq]
    exact (canonical5741 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node832 + (injectiveMoment H (mergeFirst pivotMatrix832 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix832 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix832 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value832, value146, value226, value36, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1059 = Sparse.eval value1059 (momentVector H) := by
  have heq : pivotMatrix1059 = (fun u v => node1059.transpose (pivotPermutation1059 u) v) := by apply Matrix.ext; unfold pivotMatrix1059 node1059 pivotPermutation1059; decide +kernel
  have hmoment : injectiveMoment H node1059 = injectiveMoment H pivotMatrix1059 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1059 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1059 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (0 : Fin 3) = raw4197 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw4197; decide +kernel
    rw [heq]
    exact (canonical4197 hH).trans (sound197 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) =
      Sparse.eval value202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (1 : Fin 3) = raw7539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7539; decide +kernel
    rw [heq]
    exact (canonical7539 hH).trans (sound202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1059 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1059 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1059 + (injectiveMoment H (mergeFirst pivotMatrix1059 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1059 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1059, value169, value197, value202, Sparse.eval] at hc ⊢
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

theorem sound1120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1120 = Sparse.eval value1120 (momentVector H) := by
  have heq : pivotMatrix1120 = (fun u v => node1120.transpose (pivotPermutation1120 u) v) := by apply Matrix.ext; unfold pivotMatrix1120 node1120 pivotPermutation1120; decide +kernel
  have hmoment : injectiveMoment H node1120 = injectiveMoment H pivotMatrix1120 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1120 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1120 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1120 (0 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (0 : Fin 3) = raw4211 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw4211; decide +kernel
    rw [heq]
    exact (canonical4211 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1120 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (1 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1120 (2 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1120 (2 : Fin 3) = raw7603 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1120 raw7603; decide +kernel
    rw [heq]
    exact (canonical7603 hH).trans (sound201 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1120 + (injectiveMoment H (mergeFirst pivotMatrix1120 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1120 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1120 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1120, value169, value198, value201, Sparse.eval] at hc ⊢
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

theorem sound1310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1310 = Sparse.eval value1310 (momentVector H) := by
  have heq : pivotMatrix1310 = (fun u v => node1310.transpose (pivotPermutation1310 u) v) := by apply Matrix.ext; unfold pivotMatrix1310 node1310 pivotPermutation1310; decide +kernel
  have hmoment : injectiveMoment H node1310 = injectiveMoment H pivotMatrix1310 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1310 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1310 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (0 : Fin 3) = raw6950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw6950; decide +kernel
    rw [heq]
    exact (canonical6950 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) =
      Sparse.eval value175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (1 : Fin 3) = raw8928 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8928; decide +kernel
    rw [heq]
    exact (canonical8928 hH).trans (sound175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3)) =
      Sparse.eval value167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1310 (2 : Fin 3) = raw8934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1310 raw8934; decide +kernel
    rw [heq]
    exact (canonical8934 hH).trans (sound167 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1310 + (injectiveMoment H (mergeFirst pivotMatrix1310 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1310 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1310, value167, value175, value184, Sparse.eval] at hc ⊢
  linarith

theorem sound1311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1311 = Sparse.eval value1311 (momentVector H) := by
  have heq : pivotMatrix1311 = (fun u v => node1311 (pivotPermutation1311 u) v) := by apply Matrix.ext; unfold pivotMatrix1311 node1311 pivotPermutation1311; decide +kernel
  have hmoment : injectiveMoment H node1311 = injectiveMoment H pivotMatrix1311 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1311 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1311 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (0 : Fin 3) = raw6935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw6935; decide +kernel
    rw [heq]
    exact (canonical6935 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (1 : Fin 3) = raw7585 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7585; decide +kernel
    rw [heq]
    exact (canonical7585 hH).trans (sound284 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1311 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1311 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1311 + (injectiveMoment H (mergeFirst pivotMatrix1311 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1311 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1311, value169, value203, value284, Sparse.eval] at hc ⊢
  linarith

theorem sound1315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1315 = Sparse.eval value1315 (momentVector H) := by
  have heq : pivotMatrix1315 = (fun u v => node1315.transpose (pivotPermutation1315 u) v) := by apply Matrix.ext; unfold pivotMatrix1315 node1315 pivotPermutation1315; decide +kernel
  have hmoment : injectiveMoment H node1315 = injectiveMoment H pivotMatrix1315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1315 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (0 : Fin 3) = raw7606 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw7606; decide +kernel
    rw [heq]
    exact (canonical7606 hH).trans (sound184 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (1 : Fin 3) = raw9987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9987; decide +kernel
    rw [heq]
    exact (canonical9987 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3)) =
      Sparse.eval value162 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1315 (2 : Fin 3) = raw9991 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1315 raw9991; decide +kernel
    rw [heq]
    exact (canonical9991 hH).trans (sound162 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1315 + (injectiveMoment H (mergeFirst pivotMatrix1315 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1315 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1315, value162, value169, value184, Sparse.eval] at hc ⊢
  linarith

theorem sound1316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1316 = Sparse.eval value1316 (momentVector H) := by
  have heq : pivotMatrix1316 = (fun u v => node1316 (pivotPermutation1316 u) v) := by apply Matrix.ext; unfold pivotMatrix1316 node1316 pivotPermutation1316; decide +kernel
  have hmoment : injectiveMoment H node1316 = injectiveMoment H pivotMatrix1316 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1316 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1316 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) =
      Sparse.eval value291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (0 : Fin 3) = raw7511 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7511; decide +kernel
    rw [heq]
    exact (canonical7511 hH).trans (sound291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (1 : Fin 3) = raw7590 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7590; decide +kernel
    rw [heq]
    exact (canonical7590 hH).trans (sound210 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1316 (2 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1316 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1316 + (injectiveMoment H (mergeFirst pivotMatrix1316 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1316 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1316, value169, value210, value291, Sparse.eval] at hc ⊢
  linarith

theorem sound1317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1317 = Sparse.eval value1317 (momentVector H) := by
  have heq : pivotMatrix1317 = (fun u v => node1317 (pivotPermutation1317 u) v) := by apply Matrix.ext; unfold pivotMatrix1317 node1317 pivotPermutation1317; decide +kernel
  have hmoment : injectiveMoment H node1317 = injectiveMoment H pivotMatrix1317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1317 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1317 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (0 : Fin 3) = raw7512 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7512; decide +kernel
    rw [heq]
    exact (canonical7512 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (1 : Fin 3) = raw7591 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7591; decide +kernel
    rw [heq]
    exact (canonical7591 hH).trans (sound169 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3)) =
      Sparse.eval value166 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1317 (2 : Fin 3) = raw7592 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1317 raw7592; decide +kernel
    rw [heq]
    exact (canonical7592 hH).trans (sound166 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1317 + (injectiveMoment H (mergeFirst pivotMatrix1317 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1317 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1317, value166, value169, value280, Sparse.eval] at hc ⊢
  linarith

theorem sound1320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1320 = Sparse.eval value1320 (momentVector H) := by
  have heq : pivotMatrix1320 = (fun u v => node1320 (pivotPermutation1320 u) v) := by apply Matrix.ext; unfold pivotMatrix1320 node1320 pivotPermutation1320; decide +kernel
  have hmoment : injectiveMoment H node1320 = injectiveMoment H pivotMatrix1320 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1320 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1320 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1320 (0 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (0 : Fin 3) = raw6968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw6968; decide +kernel
    rw [heq]
    exact (canonical6968 hH).trans (sound170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1320 (1 : Fin 3)) =
      Sparse.eval value269 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (1 : Fin 3) = raw7616 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw7616; decide +kernel
    rw [heq]
    exact (canonical7616 hH).trans (sound269 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1320 (2 : Fin 3)) =
      Sparse.eval value141 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1320 (2 : Fin 3) = raw7617 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1320 raw7617; decide +kernel
    rw [heq]
    exact (canonical7617 hH).trans (sound141 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1320 + (injectiveMoment H (mergeFirst pivotMatrix1320 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1320 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1320 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1320, value141, value170, value269, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound6
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node406 = Sparse.eval value406 (momentVector H) := by
  have hc : momentVector H 291 = injectiveMoment H node406 := rfl
  simp [value406, Sparse.eval, hc]

theorem sound411 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node411 = Sparse.eval value411 (momentVector H) := by
  have hc : momentVector H 300 = injectiveMoment H node411 := rfl
  simp [value411, Sparse.eval, hc]

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

theorem sound593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node593 = Sparse.eval value593 (momentVector H) := by
  have hc : momentVector H 538 = injectiveMoment H node593 := rfl
  simp [value593, Sparse.eval, hc]

theorem sound611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node611 = Sparse.eval value611 (momentVector H) := by
  have hc : momentVector H 643 = injectiveMoment H node611 := rfl
  simp [value611, Sparse.eval, hc]

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

theorem sound1369 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1369 = Sparse.eval value1369 (momentVector H) := by
  have heq : pivotMatrix1369 = (fun u v => node1369.transpose (pivotPermutation1369 u) v) := by apply Matrix.ext; unfold pivotMatrix1369 node1369 pivotPermutation1369; decide +kernel
  have hmoment : injectiveMoment H node1369 = injectiveMoment H pivotMatrix1369 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1369 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1369 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1369 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (0 : Fin 3) = raw9950 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw9950; decide +kernel
    rw [heq]
    exact (canonical9950 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1369 (1 : Fin 3)) =
      Sparse.eval value223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (1 : Fin 3) = raw10168 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw10168; decide +kernel
    rw [heq]
    exact (canonical10168 hH).trans (sound223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1369 (2 : Fin 3)) =
      Sparse.eval value196 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1369 (2 : Fin 3) = raw10172 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1369 raw10172; decide +kernel
    rw [heq]
    exact (canonical10172 hH).trans (sound196 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1369 + (injectiveMoment H (mergeFirst pivotMatrix1369 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1369 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1369 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1369, value196, value223, value280, Sparse.eval] at hc ⊢
  linarith

theorem sound1376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1376 = Sparse.eval value1376 (momentVector H) := by
  have heq : pivotMatrix1376 = (fun u v => node1376.transpose (pivotPermutation1376 u) v) := by apply Matrix.ext; unfold pivotMatrix1376 node1376 pivotPermutation1376; decide +kernel
  have hmoment : injectiveMoment H node1376 = injectiveMoment H pivotMatrix1376 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1376 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1376 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1376 (0 : Fin 3)) =
      Sparse.eval value280 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (0 : Fin 3) = raw10143 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10143; decide +kernel
    rw [heq]
    exact (canonical10143 hH).trans (sound280 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1376 (1 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (1 : Fin 3) = raw10180 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10180; decide +kernel
    rw [heq]
    exact (canonical10180 hH).trans (sound198 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1376 (2 : Fin 3)) =
      Sparse.eval value163 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1376 (2 : Fin 3) = raw10183 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1376 raw10183; decide +kernel
    rw [heq]
    exact (canonical10183 hH).trans (sound163 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1376 + (injectiveMoment H (mergeFirst pivotMatrix1376 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1376 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1376 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1376, value163, value198, value280, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound7
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node484 = Sparse.eval value484 (momentVector H) := by
  have hc : momentVector H 97 = injectiveMoment H node484 := rfl
  simp [value484, Sparse.eval, hc]

theorem sound488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node488 = Sparse.eval value488 (momentVector H) := by
  have hc : momentVector H 100 = injectiveMoment H node488 := rfl
  simp [value488, Sparse.eval, hc]

theorem sound496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node496 = Sparse.eval value496 (momentVector H) := by
  have hc : momentVector H 104 = injectiveMoment H node496 := rfl
  simp [value496, Sparse.eval, hc]

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

theorem sound2028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2028 = Sparse.eval value2028 (momentVector H) := by
  have heq : pivotMatrix2028 = (fun u v => node2028 (pivotPermutation2028 u) v) := by apply Matrix.ext; unfold pivotMatrix2028 node2028 pivotPermutation2028; decide +kernel
  have hmoment : injectiveMoment H node2028 = injectiveMoment H pivotMatrix2028 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2028 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2028 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2028 (0 : Fin 4)) =
      Sparse.eval value484 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (0 : Fin 4) = raw4745 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw4745; decide +kernel
    rw [heq]
    exact (canonical4745 hH).trans (sound484 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2028 (1 : Fin 4)) =
      Sparse.eval value488 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (1 : Fin 4) = raw3541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3541; decide +kernel
    rw [heq]
    exact (canonical3541 hH).trans (sound488 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2028 (2 : Fin 4)) =
      Sparse.eval value1120 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (2 : Fin 4) = raw3450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3450; decide +kernel
    rw [heq]
    exact (canonical3450 hH).trans (sound1120 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2028 (3 : Fin 4)) =
      Sparse.eval value411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2028 (3 : Fin 4) = raw3446 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2028 raw3446; decide +kernel
    rw [heq]
    exact (canonical3446 hH).trans (sound411 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2028 + (injectiveMoment H (mergeFirst pivotMatrix2028 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2028 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2028, value1120, value411, value484, value488, Sparse.eval] at hc ⊢
  linarith

theorem sound2029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2029 = Sparse.eval value2029 (momentVector H) := by
  have heq : pivotMatrix2029 = (fun u v => node2029 (pivotPermutation2029 u) v) := by apply Matrix.ext; unfold pivotMatrix2029 node2029 pivotPermutation2029; decide +kernel
  have hmoment : injectiveMoment H node2029 = injectiveMoment H pivotMatrix2029 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2029 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2029 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2029 (0 : Fin 4)) =
      Sparse.eval value832 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (0 : Fin 4) = raw7332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw7332; decide +kernel
    rw [heq]
    exact (canonical7332 hH).trans (sound832 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2029 (1 : Fin 4)) =
      Sparse.eval value496 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (1 : Fin 4) = raw3641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3641; decide +kernel
    rw [heq]
    exact (canonical3641 hH).trans (sound496 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2029 (2 : Fin 4)) =
      Sparse.eval value411 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (2 : Fin 4) = raw3451 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3451; decide +kernel
    rw [heq]
    exact (canonical3451 hH).trans (sound411 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2029 (3 : Fin 4)) =
      Sparse.eval value406 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2029 (3 : Fin 4) = raw3441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2029 raw3441; decide +kernel
    rw [heq]
    exact (canonical3441 hH).trans (sound406 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2029 + (injectiveMoment H (mergeFirst pivotMatrix2029 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2029 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2029, value406, value411, value496, value832, Sparse.eval] at hc ⊢
  linarith

theorem sound2037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2037 = Sparse.eval value2037 (momentVector H) := by
  have heq : pivotMatrix2037 = (fun u v => node2037 (pivotPermutation2037 u) v) := by apply Matrix.ext; unfold pivotMatrix2037 node2037 pivotPermutation2037; decide +kernel
  have hmoment : injectiveMoment H node2037 = injectiveMoment H pivotMatrix2037 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2037 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2037 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2037 (0 : Fin 4)) =
      Sparse.eval value1369 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (0 : Fin 4) = raw4832 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw4832; decide +kernel
    rw [heq]
    exact (canonical4832 hH).trans (sound1369 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2037 (1 : Fin 4)) =
      Sparse.eval value1376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (1 : Fin 4) = raw3614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3614; decide +kernel
    rw [heq]
    exact (canonical3614 hH).trans (sound1376 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2037 (2 : Fin 4)) =
      Sparse.eval value1320 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (2 : Fin 4) = raw3519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3519; decide +kernel
    rw [heq]
    exact (canonical3519 hH).trans (sound1320 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2037 (3 : Fin 4)) =
      Sparse.eval value611 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2037 (3 : Fin 4) = raw3516 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2037 raw3516; decide +kernel
    rw [heq]
    exact (canonical3516 hH).trans (sound611 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2037 + (injectiveMoment H (mergeFirst pivotMatrix2037 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2037 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2037, value1320, value1369, value1376, value611, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound34
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2216 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2216 = Sparse.eval value2216 (momentVector H) := by
  have heq : pivotMatrix2216 = (fun u v => node2216 (pivotPermutation2216 u) v) := by apply Matrix.ext; unfold pivotMatrix2216 node2216 pivotPermutation2216; decide +kernel
  have hmoment : injectiveMoment H node2216 = injectiveMoment H pivotMatrix2216 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2216 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2216 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) =
      Sparse.eval value1315 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (0 : Fin 4) = raw5329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw5329; decide +kernel
    rw [heq]
    exact (canonical5329 hH).trans (sound1315 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) =
      Sparse.eval value1310 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (1 : Fin 4) = raw4609 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4609; decide +kernel
    rw [heq]
    exact (canonical4609 hH).trans (sound1310 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) =
      Sparse.eval value1317 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (2 : Fin 4) = raw4504 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4504; decide +kernel
    rw [heq]
    exact (canonical4504 hH).trans (sound1317 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2216 (3 : Fin 4) = raw4501 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2216 raw4501; decide +kernel
    rw [heq]
    exact (canonical4501 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2216 + (injectiveMoment H (mergeFirst pivotMatrix2216 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2216 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2216, value1310, value1315, value1317, value593, Sparse.eval] at hc ⊢
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

theorem sound2762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2762 = Sparse.eval value2762 (momentVector H) := by
  have heq : pivotMatrix2762 = (fun u v => node2762 (pivotPermutation2762 u) v) := by apply Matrix.ext; unfold pivotMatrix2762 node2762 pivotPermutation2762; decide +kernel
  have hmoment : injectiveMoment H node2762 = injectiveMoment H pivotMatrix2762 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2762 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2762 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2762 (0 : Fin 4)) =
      Sparse.eval value1059 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (0 : Fin 4) = raw6509 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw6509; decide +kernel
    rw [heq]
    exact (canonical6509 hH).trans (sound1059 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2762 (1 : Fin 4)) =
      Sparse.eval value1311 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (1 : Fin 4) = raw8368 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8368; decide +kernel
    rw [heq]
    exact (canonical8368 hH).trans (sound1311 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2762 (2 : Fin 4)) =
      Sparse.eval value1316 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (2 : Fin 4) = raw8489 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8489; decide +kernel
    rw [heq]
    exact (canonical8489 hH).trans (sound1316 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2762 (3 : Fin 4)) =
      Sparse.eval value169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2762 (3 : Fin 4) = raw8498 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2762 raw8498; decide +kernel
    rw [heq]
    exact (canonical8498 hH).trans (sound169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2762 + (injectiveMoment H (mergeFirst pivotMatrix2762 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2762 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2762, value1059, value1311, value1316, value169, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound49
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3176_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3176 = Sparse.eval value3176 (momentVector H) := by
  have heq : pivotMatrix3176 = (fun u v => node3176 (pivotPermutation3176 u) v) := by apply Matrix.ext; unfold pivotMatrix3176 node3176 pivotPermutation3176; decide +kernel
  have hmoment : injectiveMoment H node3176 = injectiveMoment H pivotMatrix3176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3176 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3176 (0 : Fin 5)) =
      Sparse.eval value2216 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (0 : Fin 5) = raw4493 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw4493; decide +kernel
    rw [heq]
    exact (canonical4493 hH).trans (sound2216 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3176 (1 : Fin 5)) =
      Sparse.eval value2037 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (1 : Fin 5) = raw3510 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3510; decide +kernel
    rw [heq]
    exact (canonical3510 hH).trans (sound2037 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3176 (2 : Fin 5)) =
      Sparse.eval value2029 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (2 : Fin 5) = raw3440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3440; decide +kernel
    rw [heq]
    exact (canonical3440 hH).trans (sound2029 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3176 (3 : Fin 5)) =
      Sparse.eval value2762 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (3 : Fin 5) = raw3433 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3433; decide +kernel
    rw [heq]
    exact (canonical3433 hH).trans (sound2762 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3176 (4 : Fin 5)) =
      Sparse.eval value2028 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3176 (4 : Fin 5) = raw3432 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3176 raw3432; decide +kernel
    rw [heq]
    exact (canonical3432 hH).trans (sound2028 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3176 + (injectiveMoment H (mergeFirst pivotMatrix3176 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3176 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3176, value2028, value2029, value2037, value2216, value2762, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3176_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3176_e_oai
