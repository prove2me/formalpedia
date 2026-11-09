-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3361_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T11:10:20.36519+00:00
-- url     : https://prove2.me/submissions/ed660179-6a97-4030-a745-a7ce0567c25a

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
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2546_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3236 = injectiveMoment H node1282 := by
  calc
    injectiveMoment H raw3236 = injectiveMoment H raw3236step0 := by
      have heq : raw3236step0 = -raw3236 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3236).symm
    injectiveMoment H raw3236step0 = injectiveMoment H raw3236step1 := by
      have heq : raw3236step1 = (fun i j => raw3236step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3236step0 permutation19 permutation15
    _ = injectiveMoment H node1282 := by rfl

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

theorem canonical6144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6144 = injectiveMoment H node2516 := by
  rfl

theorem canonical6145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6145 = injectiveMoment H node2546 := by
  calc
    injectiveMoment H raw6145 = injectiveMoment H raw6145step0 := by
      have heq : raw6145step0 = (fun i j => raw6145 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6145 permutation36 permutation15
    _ = injectiveMoment H node2546 := by rfl

theorem canonical6146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6146 = injectiveMoment H node953 := by
  calc
    injectiveMoment H raw6146 = injectiveMoment H raw6146step0 := by
      have heq : raw6146step0 = (fun i j => raw6146 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6146 permutation10 permutation15
    _ = injectiveMoment H node953 := by rfl

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

theorem canonical6158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6158 = injectiveMoment H node948 := by
  calc
    injectiveMoment H raw6158 = injectiveMoment H raw6158step0 := by
      have heq : raw6158step0 = (fun i j => raw6158 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6158 permutation9 permutation15
    _ = injectiveMoment H node948 := by rfl

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

theorem canonical6192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6192 = injectiveMoment H node2526 := by
  calc
    injectiveMoment H raw6192 = injectiveMoment H raw6192step0 := by
      have heq : raw6192step0 = (fun i j => raw6192 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6192 permutation49 permutation15
    _ = injectiveMoment H node2526 := by rfl

theorem canonical6199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6199 = injectiveMoment H node604 := by
  calc
    injectiveMoment H raw6199 = injectiveMoment H raw6199step0 := by
      have heq : raw6199step0 = raw6199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6199).symm
    injectiveMoment H raw6199step0 = injectiveMoment H raw6199step1 := by
      have heq : raw6199step1 = (fun i j => raw6199step0 (permutation23 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6199step0 permutation23 permutation29
    _ = injectiveMoment H node604 := by rfl

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

theorem canonical6226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6226 = injectiveMoment H node948 := by
  rfl

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

theorem canonical6304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6304 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6304 = injectiveMoment H raw6304step0 := by
      have heq : raw6304step0 = raw6304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6304).symm
    injectiveMoment H raw6304step0 = injectiveMoment H raw6304step1 := by
      have heq : raw6304step1 = (fun i j => raw6304step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6304step0 permutation21 permutation5
    _ = injectiveMoment H node173 := by rfl

theorem canonical6318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6318 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw6318 = injectiveMoment H raw6318step0 := by
      have heq : raw6318step0 = (fun i j => raw6318 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6318 permutation12 permutation15
    _ = injectiveMoment H node977 := by rfl

theorem canonical6323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6323 = injectiveMoment H node982 := by
  calc
    injectiveMoment H raw6323 = injectiveMoment H raw6323step0 := by
      have heq : raw6323step0 = (fun i j => raw6323 (permutation13 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6323 permutation13 permutation9
    _ = injectiveMoment H node982 := by rfl

theorem canonical6324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6324 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6324 = injectiveMoment H raw6324step0 := by
      have heq : raw6324step0 = raw6324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6324).symm
    injectiveMoment H raw6324step0 = injectiveMoment H raw6324step1 := by
      have heq : raw6324step1 = (fun i j => raw6324step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6324step0 permutation28 permutation6
    _ = injectiveMoment H node271 := by rfl

theorem canonical6330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6330 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6330 = injectiveMoment H raw6330step0 := by
      have heq : raw6330step0 = raw6330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6330).symm
    injectiveMoment H raw6330step0 = injectiveMoment H raw6330step1 := by
      have heq : raw6330step1 = (fun i j => raw6330step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6330step0 permutation22 permutation5
    _ = injectiveMoment H node170 := by rfl

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

theorem canonical6338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6338 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6338 = injectiveMoment H raw6338step0 := by
      have heq : raw6338step0 = raw6338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6338).symm
    injectiveMoment H raw6338step0 = injectiveMoment H raw6338step1 := by
      have heq : raw6338step1 = (fun i j => raw6338step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6338step0 permutation21 permutation7
    _ = injectiveMoment H node173 := by rfl

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

theorem canonical6530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6530 = injectiveMoment H node1079 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical6576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6576 = injectiveMoment H node262 := by
  calc
    injectiveMoment H raw6576 = injectiveMoment H raw6576step0 := by
      have heq : raw6576step0 = raw6576.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6576).symm
    _ = injectiveMoment H node262 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6594 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6594 = injectiveMoment H raw6594step0 := by
      have heq : raw6594step0 = raw6594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6594).symm
    injectiveMoment H raw6594step0 = injectiveMoment H raw6594step1 := by
      have heq : raw6594step1 = (fun i j => raw6594step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6594step0 permutation16 permutation4
    _ = injectiveMoment H node261 := by rfl

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

theorem canonical6898 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6898 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw6898 = injectiveMoment H raw6898step0 := by
      have heq : raw6898step0 = raw6898.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6898).symm
    injectiveMoment H raw6898step0 = injectiveMoment H raw6898step1 := by
      have heq : raw6898step1 = -raw6898step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6898step0).symm
    injectiveMoment H raw6898step1 = injectiveMoment H raw6898step2 := by
      have heq : raw6898step2 = (fun i j => raw6898step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6898step1 permutation26 permutation3
    _ = injectiveMoment H node209 := by rfl

theorem canonical6908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6908 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw6908 = injectiveMoment H raw6908step0 := by
      have heq : raw6908step0 = raw6908.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6908).symm
    injectiveMoment H raw6908step0 = injectiveMoment H raw6908step1 := by
      have heq : raw6908step1 = -raw6908step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6908step0).symm
    injectiveMoment H raw6908step1 = injectiveMoment H raw6908step2 := by
      have heq : raw6908step2 = (fun i j => raw6908step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6908step1 permutation26 permutation3
    _ = injectiveMoment H node184 := by rfl

theorem canonical6911 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6911 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw6911 = injectiveMoment H raw6911step0 := by
      have heq : raw6911step0 = raw6911.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6911).symm
    injectiveMoment H raw6911step0 = injectiveMoment H raw6911step1 := by
      have heq : raw6911step1 = -raw6911step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6911step0).symm
    injectiveMoment H raw6911step1 = injectiveMoment H raw6911step2 := by
      have heq : raw6911step2 = (fun i j => raw6911step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6911step1 permutation26 permutation3
    _ = injectiveMoment H node212 := by rfl

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

theorem canonical6936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6936 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw6936 = injectiveMoment H raw6936step0 := by
      have heq : raw6936step0 = raw6936.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6936).symm
    injectiveMoment H raw6936step0 = injectiveMoment H raw6936step1 := by
      have heq : raw6936step1 = -raw6936step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6936step0).symm
    injectiveMoment H raw6936step1 = injectiveMoment H raw6936step2 := by
      have heq : raw6936step2 = (fun i j => raw6936step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6936step1 permutation26 permutation3
    _ = injectiveMoment H node187 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7101 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw7101 = injectiveMoment H raw7101step0 := by
      have hz : ∀ i, raw7101 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7101step0 = (fun i j => raw7101 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7101 permutation15 hz
    _ = injectiveMoment H node56 := by rfl

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

theorem canonical7117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7117 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7117 = injectiveMoment H raw7117step0 := by
      have heq : raw7117step0 = raw7117.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7117).symm
    injectiveMoment H raw7117step0 = injectiveMoment H raw7117step1 := by
      have heq : raw7117step1 = (fun i j => raw7117step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7117step0 permutation28 permutation6
    _ = injectiveMoment H node272 := by rfl

theorem canonical7135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7135 = injectiveMoment H node2726 := by
  calc
    injectiveMoment H raw7135 = injectiveMoment H raw7135step0 := by
      have heq : raw7135step0 = -raw7135 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7135).symm
    injectiveMoment H raw7135step0 = injectiveMoment H raw7135step1 := by
      have heq : raw7135step1 = (fun i j => raw7135step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7135step0 permutation98 permutation16
    _ = injectiveMoment H node2726 := by rfl

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

theorem canonical7199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7199 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw7199 = injectiveMoment H raw7199step0 := by
      have heq : raw7199step0 = raw7199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7199).symm
    injectiveMoment H raw7199step0 = injectiveMoment H raw7199step1 := by
      have heq : raw7199step1 = -raw7199step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7199step0).symm
    injectiveMoment H raw7199step1 = injectiveMoment H raw7199step2 := by
      have heq : raw7199step2 = (fun i j => raw7199step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7199step1 permutation27 permutation19
    _ = injectiveMoment H node1202 := by rfl

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

theorem canonical7223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7223 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7223 = injectiveMoment H raw7223step0 := by
      have hz : ∀ i, raw7223 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7223step0 = (fun i j => raw7223 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7223 permutation15 hz
    _ = injectiveMoment H node63 := by rfl

theorem canonical7225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7225 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw7225 = injectiveMoment H raw7225step0 := by
      have heq : raw7225step0 = (fun i j => raw7225 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7225 permutation11 permutation9
    _ = injectiveMoment H node1267 := by rfl

theorem canonical7228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7228 = injectiveMoment H node1277 := by
  rfl

theorem canonical7231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7231 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7231 = injectiveMoment H raw7231step0 := by
      have heq : raw7231step0 = raw7231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7231).symm
    injectiveMoment H raw7231step0 = injectiveMoment H raw7231step1 := by
      have heq : raw7231step1 = (fun i j => raw7231step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7231step0 permutation21 permutation5
    _ = injectiveMoment H node174 := by rfl

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

theorem canonical7249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7249 = injectiveMoment H node174 := by
  calc
    injectiveMoment H raw7249 = injectiveMoment H raw7249step0 := by
      have heq : raw7249step0 = raw7249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7249).symm
    injectiveMoment H raw7249step0 = injectiveMoment H raw7249step1 := by
      have heq : raw7249step1 = (fun i j => raw7249step0 (permutation21 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7249step0 permutation21 permutation7
    _ = injectiveMoment H node174 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical247
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical8030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8030 = injectiveMoment H node1011 := by
  calc
    injectiveMoment H raw8030 = injectiveMoment H raw8030step0 := by
      have heq : raw8030step0 = -raw8030 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8030).symm
    injectiveMoment H raw8030step0 = injectiveMoment H raw8030step1 := by
      have heq : raw8030step1 = (fun i j => raw8030step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8030step0 permutation31 permutation9
    _ = injectiveMoment H node1011 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw840 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw840 = injectiveMoment H raw840step0 := by
      have heq : raw840step0 = (fun i j => raw840 (permutation5 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw840 permutation5 permutation7
    _ = injectiveMoment H node43 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8337 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8337 = injectiveMoment H raw8337step0 := by
      have hz : ∀ i, raw8337 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8337step0 = (fun i j => raw8337 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8337 permutation9 hz
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical8910 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8910 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw8910 = injectiveMoment H raw8910step0 := by
      have heq : raw8910step0 = raw8910.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8910).symm
    injectiveMoment H raw8910step0 = injectiveMoment H raw8910step1 := by
      have heq : raw8910step1 = -raw8910step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8910step0).symm
    injectiveMoment H raw8910step1 = injectiveMoment H raw8910step2 := by
      have heq : raw8910step2 = (fun i j => raw8910step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8910step1 permutation21 permutation3
    _ = injectiveMoment H node180 := by rfl

theorem canonical8924 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8924 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8924 = injectiveMoment H raw8924step0 := by
      have heq : raw8924step0 = -raw8924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8924).symm
    injectiveMoment H raw8924step0 = injectiveMoment H raw8924step1 := by
      have hz : ∀ i, raw8924step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8924step1 = (fun i j => raw8924step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8924step0 permutation9 hz
    injectiveMoment H raw8924step1 = injectiveMoment H raw8924step2 := by
      have heq : raw8924step2 = (fun i j => raw8924step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8924step1 permutation5 permutation3
    _ = injectiveMoment H node40 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2147 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2147 = injectiveMoment H raw2147step0 := by
      have heq : raw2147step0 = raw2147.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2147).symm
    injectiveMoment H raw2147step0 = injectiveMoment H raw2147step1 := by
      have heq : raw2147step1 = -raw2147step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2147step0).symm
    injectiveMoment H raw2147step1 = injectiveMoment H raw2147step2 := by
      have heq : raw2147step2 = (fun i j => raw2147step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2147step1 permutation19 permutation5
    _ = injectiveMoment H node103 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2530 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2530 = injectiveMoment H raw2530step0 := by
      have heq : raw2530step0 = raw2530.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2530).symm
    injectiveMoment H raw2530step0 = injectiveMoment H raw2530step1 := by
      have heq : raw2530step1 = -raw2530step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2530step0).symm
    injectiveMoment H raw2530step1 = injectiveMoment H raw2530step2 := by
      have heq : raw2530step2 = (fun i j => raw2530step1 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2530step1 permutation17 permutation5
    _ = injectiveMoment H node103 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2636 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2636 = injectiveMoment H raw2636step0 := by
      have heq : raw2636step0 = raw2636.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2636).symm
    injectiveMoment H raw2636step0 = injectiveMoment H raw2636step1 := by
      have heq : raw2636step1 = (fun i j => raw2636step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2636step0 permutation28 permutation5
    _ = injectiveMoment H node103 := by rfl

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

theorem canonical2865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2865 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw2865 = injectiveMoment H raw2865step0 := by
      have heq : raw2865step0 = (fun i j => raw2865 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2865 permutation4 permutation3
    _ = injectiveMoment H node40 := by rfl

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

theorem sound103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node103 = Sparse.eval value103 (momentVector H) := by
  have hc : momentVector H 64 = injectiveMoment H node103 := rfl
  simp [value103, Sparse.eval, hc]

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

theorem sound173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node173 = Sparse.eval value173 (momentVector H) := by
  have heq : pivotMatrix173 = (fun u v => node173 (pivotPermutation173 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node173 = injectiveMoment H pivotMatrix173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix173 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix173 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node173 + (injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value173, value40, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node174 = Sparse.eval value174 (momentVector H) := by
  have heq : pivotMatrix174 = (fun u v => node174 (pivotPermutation174 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node174 = injectiveMoment H pivotMatrix174 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix174 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix174 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix174 (2 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node174 + (injectiveMoment H (mergeFirst pivotMatrix174 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix174 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value174, value52, value56, value63, Sparse.eval] at hc ⊢
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

theorem sound180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node180 = Sparse.eval value180 (momentVector H) := by
  have heq : pivotMatrix180 = (fun u v => node180 (pivotPermutation180 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node180 = injectiveMoment H pivotMatrix180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix180 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix180 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (0 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (1 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix180 (2 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node180 + (injectiveMoment H (mergeFirst pivotMatrix180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value180, value36, value40, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node184 = Sparse.eval value184 (momentVector H) := by
  have hc : momentVector H 51 = injectiveMoment H node184 := rfl
  simp [value184, Sparse.eval, hc]

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

theorem sound187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node187 = Sparse.eval value187 (momentVector H) := by
  have heq : pivotMatrix187 = (fun u v => node187 (pivotPermutation187 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node187 = injectiveMoment H pivotMatrix187 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix187 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix187 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (1 : Fin 3) = raw2865 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2865 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix187 (2 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node187 + (injectiveMoment H (mergeFirst pivotMatrix187 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix187 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value187, value37, value40, value63, Sparse.eval] at hc ⊢
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

theorem sound209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node209 = Sparse.eval value209 (momentVector H) := by
  have heq : pivotMatrix209 = (fun u v => node209 (pivotPermutation209 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node209 = injectiveMoment H pivotMatrix209 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix209 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix209 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix209 (0 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (0 : Fin 3) = raw4965 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4965 hH).trans (sound43 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix209 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (1 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix209 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix209 (2 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node209 + (injectiveMoment H (mergeFirst pivotMatrix209 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix209 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix209 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value209, value32, value36, value43, Sparse.eval] at hc ⊢
  linarith

theorem sound212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node212 = Sparse.eval value212 (momentVector H) := by
  have hc : momentVector H 55 = injectiveMoment H node212 := rfl
  simp [value212, Sparse.eval, hc]

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

theorem sound262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node262 = Sparse.eval value262 (momentVector H) := by
  have hc : momentVector H 238 = injectiveMoment H node262 := rfl
  simp [value262, Sparse.eval, hc]

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

theorem sound948 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node948 = Sparse.eval value948 (momentVector H) := by
  have heq : pivotMatrix948 = (fun u v => node948.transpose (pivotPermutation948 u) v) := by apply Matrix.ext; unfold pivotMatrix948 node948 pivotPermutation948; decide +kernel
  have hmoment : injectiveMoment H node948 = injectiveMoment H pivotMatrix948 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix948 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix948 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix948 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (0 : Fin 3) = raw2147 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw2147; decide +kernel
    rw [heq]
    exact (canonical2147 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix948 (1 : Fin 3)) =
      Sparse.eval value262 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (1 : Fin 3) = raw6576 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw6576; decide +kernel
    rw [heq]
    exact (canonical6576 hH).trans (sound262 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix948 (2 : Fin 3)) =
      Sparse.eval value261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix948 (2 : Fin 3) = raw6594 := by apply Matrix.ext; unfold mergeFirst pivotMatrix948 raw6594; decide +kernel
    rw [heq]
    exact (canonical6594 hH).trans (sound261 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node948 + (injectiveMoment H (mergeFirst pivotMatrix948 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix948 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix948 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value948, value103, value261, value262, Sparse.eval] at hc ⊢
  linarith

theorem sound953 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node953 = Sparse.eval value953 (momentVector H) := by
  have heq : pivotMatrix953 = (fun u v => node953.transpose (pivotPermutation953 u) v) := by apply Matrix.ext; unfold pivotMatrix953 node953 pivotPermutation953; decide +kernel
  have hmoment : injectiveMoment H node953 = injectiveMoment H pivotMatrix953 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix953 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix953 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix953 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (0 : Fin 3) = raw2530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw2530; decide +kernel
    rw [heq]
    exact (canonical2530 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix953 (1 : Fin 3)) =
      Sparse.eval value209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (1 : Fin 3) = raw6898 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw6898; decide +kernel
    rw [heq]
    exact (canonical6898 hH).trans (sound209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix953 (2 : Fin 3)) =
      Sparse.eval value212 (momentVector H) := by
    have heq : mergeFirst pivotMatrix953 (2 : Fin 3) = raw6911 := by apply Matrix.ext; unfold mergeFirst pivotMatrix953 raw6911; decide +kernel
    rw [heq]
    exact (canonical6911 hH).trans (sound212 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node953 + (injectiveMoment H (mergeFirst pivotMatrix953 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix953 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix953 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value953, value103, value209, value212, Sparse.eval] at hc ⊢
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

theorem sound977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node977 = Sparse.eval value977 (momentVector H) := by
  have heq : pivotMatrix977 = (fun u v => node977 (pivotPermutation977 u) v) := by apply Matrix.ext; unfold pivotMatrix977 node977 pivotPermutation977; decide +kernel
  have hmoment : injectiveMoment H node977 = injectiveMoment H pivotMatrix977 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix977 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix977 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (1 : Fin 3) = raw6338 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6338; decide +kernel
    rw [heq]
    exact (canonical6338 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3)) =
      Sparse.eval value188 (momentVector H) := by
    have heq : mergeFirst pivotMatrix977 (2 : Fin 3) = raw6298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix977 raw6298; decide +kernel
    rw [heq]
    exact (canonical6298 hH).trans (sound188 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node977 + (injectiveMoment H (mergeFirst pivotMatrix977 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix977 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value977, value173, value188, value63, Sparse.eval] at hc ⊢
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

theorem sound982 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node982 = Sparse.eval value982 (momentVector H) := by
  have heq : pivotMatrix982 = (fun u v => node982 (pivotPermutation982 u) v) := by apply Matrix.ext; unfold pivotMatrix982 node982 pivotPermutation982; decide +kernel
  have hmoment : injectiveMoment H node982 = injectiveMoment H pivotMatrix982 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix982 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix982 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (0 : Fin 3) = raw7231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw7231; decide +kernel
    rw [heq]
    exact (canonical7231 hH).trans (sound174 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) =
      Sparse.eval value170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (1 : Fin 3) = raw6330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6330; decide +kernel
    rw [heq]
    exact (canonical6330 hH).trans (sound170 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix982 (2 : Fin 3) = raw6304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix982 raw6304; decide +kernel
    rw [heq]
    exact (canonical6304 hH).trans (sound173 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node982 + (injectiveMoment H (mergeFirst pivotMatrix982 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix982 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value982, value170, value173, value174, Sparse.eval] at hc ⊢
  linarith

theorem sound1011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1011 = Sparse.eval value1011 (momentVector H) := by
  have heq : pivotMatrix1011 = (fun u v => node1011.transpose (pivotPermutation1011 u) v) := by apply Matrix.ext; unfold pivotMatrix1011 node1011 pivotPermutation1011; decide +kernel
  have hmoment : injectiveMoment H node1011 = injectiveMoment H pivotMatrix1011 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1011 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1011 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1011 (0 : Fin 3)) =
      Sparse.eval value103 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (0 : Fin 3) = raw2636 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw2636; decide +kernel
    rw [heq]
    exact (canonical2636 hH).trans (sound103 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1011 (1 : Fin 3)) =
      Sparse.eval value184 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (1 : Fin 3) = raw6908 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw6908; decide +kernel
    rw [heq]
    exact (canonical6908 hH).trans (sound184 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1011 (2 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1011 (2 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1011 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1011 + (injectiveMoment H (mergeFirst pivotMatrix1011 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1011 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1011 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1011, value103, value184, value187, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound16
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound18
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1202 = Sparse.eval value1202 (momentVector H) := by
  have heq : pivotMatrix1202 = (fun u v => node1202 (pivotPermutation1202 u) v) := by apply Matrix.ext; unfold pivotMatrix1202 node1202 pivotPermutation1202; decide +kernel
  have hmoment : injectiveMoment H node1202 = injectiveMoment H pivotMatrix1202 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1202 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1202 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (0 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (1 : Fin 3) = raw7101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7101; decide +kernel
    rw [heq]
    exact (canonical7101 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3)) =
      Sparse.eval value272 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1202 (2 : Fin 3) = raw7117 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1202 raw7117; decide +kernel
    rw [heq]
    exact (canonical7117 hH).trans (sound272 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1202 + (injectiveMoment H (mergeFirst pivotMatrix1202 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1202 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1202, value271, value272, value56, Sparse.eval] at hc ⊢
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

theorem sound1267 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1267 = Sparse.eval value1267 (momentVector H) := by
  have heq : pivotMatrix1267 = (fun u v => node1267 (pivotPermutation1267 u) v) := by apply Matrix.ext; unfold pivotMatrix1267 node1267 pivotPermutation1267; decide +kernel
  have hmoment : injectiveMoment H node1267 = injectiveMoment H pivotMatrix1267 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1267 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1267 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (0 : Fin 3) = raw8337 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw8337; decide +kernel
    rw [heq]
    exact (canonical8337 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) =
      Sparse.eval value174 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (1 : Fin 3) = raw7249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7249; decide +kernel
    rw [heq]
    exact (canonical7249 hH).trans (sound174 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1267 (2 : Fin 3) = raw7223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1267 raw7223; decide +kernel
    rw [heq]
    exact (canonical7223 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1267 + (injectiveMoment H (mergeFirst pivotMatrix1267 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1267 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1267, value174, value63, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1282 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1282 = Sparse.eval value1282 (momentVector H) := by
  have heq : pivotMatrix1282 = (fun u v => node1282 (pivotPermutation1282 u) v) := by apply Matrix.ext; unfold pivotMatrix1282 node1282 pivotPermutation1282; decide +kernel
  have hmoment : injectiveMoment H node1282 = injectiveMoment H pivotMatrix1282 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1282 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1282 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1282 (0 : Fin 3)) =
      Sparse.eval value187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (0 : Fin 3) = raw6936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw6936; decide +kernel
    rw [heq]
    exact (canonical6936 hH).trans (sound187 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1282 (1 : Fin 3)) =
      Sparse.eval value180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (1 : Fin 3) = raw8910 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw8910; decide +kernel
    rw [heq]
    exact (canonical8910 hH).trans (sound180 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1282 (2 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1282 (2 : Fin 3) = raw8924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1282 raw8924; decide +kernel
    rw [heq]
    exact (canonical8924 hH).trans (sound40 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1282 + (injectiveMoment H (mergeFirst pivotMatrix1282 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1282 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1282 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1282, value180, value187, value40, Sparse.eval] at hc ⊢
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

theorem sound604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node604 = Sparse.eval value604 (momentVector H) := by
  have hc : momentVector H 546 = injectiveMoment H node604 := rfl
  simp [value604, Sparse.eval, hc]

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

theorem sound2516 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2516 = Sparse.eval value2516 (momentVector H) := by
  have heq : pivotMatrix2516 = (fun u v => node2516 (pivotPermutation2516 u) v) := by apply Matrix.ext; unfold pivotMatrix2516 node2516 pivotPermutation2516; decide +kernel
  have hmoment : injectiveMoment H node2516 = injectiveMoment H pivotMatrix2516 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2516 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2516 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2516 (0 : Fin 4)) =
      Sparse.eval value1011 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (0 : Fin 4) = raw8030 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw8030; decide +kernel
    rw [heq]
    exact (canonical8030 hH).trans (sound1011 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2516 (1 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (1 : Fin 4) = raw6226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6226; decide +kernel
    rw [heq]
    exact (canonical6226 hH).trans (sound948 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2516 (2 : Fin 4)) =
      Sparse.eval value948 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (2 : Fin 4) = raw6158 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6158; decide +kernel
    rw [heq]
    exact (canonical6158 hH).trans (sound948 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2516 (3 : Fin 4)) =
      Sparse.eval value953 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2516 (3 : Fin 4) = raw6146 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2516 raw6146; decide +kernel
    rw [heq]
    exact (canonical6146 hH).trans (sound953 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2516 + (injectiveMoment H (mergeFirst pivotMatrix2516 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2516 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2516, value1011, value948, value953, Sparse.eval] at hc ⊢
  linarith

theorem sound2526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2526 = Sparse.eval value2526 (momentVector H) := by
  have heq : pivotMatrix2526 = (fun u v => node2526 (pivotPermutation2526 u) v) := by apply Matrix.ext; unfold pivotMatrix2526 node2526 pivotPermutation2526; decide +kernel
  have hmoment : injectiveMoment H node2526 = injectiveMoment H pivotMatrix2526 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2526 0 = Pi.single (1 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2526 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2526 (0 : Fin 4)) =
      Sparse.eval value1282 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (0 : Fin 4) = raw3236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw3236; decide +kernel
    rw [heq]
    exact (canonical3236 hH).trans (sound1282 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2526 (1 : Fin 4)) =
      Sparse.eval value604 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (1 : Fin 4) = raw6199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6199; decide +kernel
    rw [heq]
    exact (canonical6199 hH).trans (sound604 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2526 (2 : Fin 4)) =
      Sparse.eval value977 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (2 : Fin 4) = raw6318 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6318; decide +kernel
    rw [heq]
    exact (canonical6318 hH).trans (sound977 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2526 (3 : Fin 4)) =
      Sparse.eval value982 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2526 (3 : Fin 4) = raw6323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2526 raw6323; decide +kernel
    rw [heq]
    exact (canonical6323 hH).trans (sound982 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2526 + (injectiveMoment H (mergeFirst pivotMatrix2526 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2526 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2526, value1282, value604, value977, value982, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound42
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2726 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2726 = Sparse.eval value2726 (momentVector H) := by
  have heq : pivotMatrix2726 = (fun u v => node2726 (pivotPermutation2726 u) v) := by apply Matrix.ext; unfold pivotMatrix2726 node2726 pivotPermutation2726; decide +kernel
  have hmoment : injectiveMoment H node2726 = injectiveMoment H pivotMatrix2726 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2726 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2726 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2726 (0 : Fin 4)) =
      Sparse.eval value1079 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (0 : Fin 4) = raw6530 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw6530; decide +kernel
    rw [heq]
    exact (canonical6530 hH).trans (sound1079 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2726 (1 : Fin 4)) =
      Sparse.eval value1202 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (1 : Fin 4) = raw7199 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7199; decide +kernel
    rw [heq]
    exact (canonical7199 hH).trans (sound1202 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2726 (2 : Fin 4)) =
      Sparse.eval value1267 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (2 : Fin 4) = raw7225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7225; decide +kernel
    rw [heq]
    exact (canonical7225 hH).trans (sound1267 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2726 (3 : Fin 4)) =
      Sparse.eval value1277 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2726 (3 : Fin 4) = raw7228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2726 raw7228; decide +kernel
    rw [heq]
    exact (canonical7228 hH).trans (sound1277 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2726 + (injectiveMoment H (mergeFirst pivotMatrix2726 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2726 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2726, value1079, value1202, value1267, value1277, Sparse.eval] at hc ⊢
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

theorem sound3361_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3361 = Sparse.eval value3361 (momentVector H) := by
  have heq : pivotMatrix3361 = (fun u v => node3361 (pivotPermutation3361 u) v) := by apply Matrix.ext; unfold pivotMatrix3361 node3361 pivotPermutation3361; decide +kernel
  have hmoment : injectiveMoment H node3361 = injectiveMoment H pivotMatrix3361 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3361 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3361 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3361 (0 : Fin 5)) =
      Sparse.eval value2726 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3361 (0 : Fin 5) = raw7135 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3361 raw7135; decide +kernel
    rw [heq]
    exact (canonical7135 hH).trans (sound2726 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3361 (1 : Fin 5)) =
      Sparse.eval value2526 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3361 (1 : Fin 5) = raw6192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3361 raw6192; decide +kernel
    rw [heq]
    exact (canonical6192 hH).trans (sound2526 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3361 (2 : Fin 5)) =
      Sparse.eval value2020 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3361 (2 : Fin 5) = raw6153 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3361 raw6153; decide +kernel
    rw [heq]
    exact (canonical6153 hH).trans (sound2020 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3361 (3 : Fin 5)) =
      Sparse.eval value2546 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3361 (3 : Fin 5) = raw6145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3361 raw6145; decide +kernel
    rw [heq]
    exact (canonical6145 hH).trans (sound2546_e hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3361 (4 : Fin 5)) =
      Sparse.eval value2516 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3361 (4 : Fin 5) = raw6144 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3361 raw6144; decide +kernel
    rw [heq]
    exact (canonical6144 hH).trans (sound2516 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3361 + (injectiveMoment H (mergeFirst pivotMatrix3361 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3361 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3361 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3361 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3361 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3361, value2020, value2516, value2526, value2546, value2726, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3361_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3361_e_oai
