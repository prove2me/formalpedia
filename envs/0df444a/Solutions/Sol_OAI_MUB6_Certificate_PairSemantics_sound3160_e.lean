-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSemantics.sound3160_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T06:30:00.295088+00:00
-- url     : https://prove2.me/submissions/911825d5-4ea2-4ea2-8c65-ec116e980344

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw333 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw333 = injectiveMoment H raw333step0 := by
      have heq : raw333step0 = -raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw333).symm
    injectiveMoment H raw333step0 = injectiveMoment H raw333step1 := by
      have heq : raw333step1 = (fun i j => raw333step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw333step0 permutation6 permutation5
    _ = injectiveMoment H node40 := by rfl

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

theorem canonical3357 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3357 = injectiveMoment H node2005 := by
  rfl

theorem canonical3358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3358 = injectiveMoment H node2683 := by
  calc
    injectiveMoment H raw3358 = injectiveMoment H raw3358step0 := by
      have heq : raw3358step0 = -raw3358 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3358).symm
    injectiveMoment H raw3358step0 = injectiveMoment H raw3358step1 := by
      have heq : raw3358step1 = (fun i j => raw3358step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3358step0 permutation96 permutation15
    _ = injectiveMoment H node2683 := by rfl

theorem canonical3359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3359 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw3359 = injectiveMoment H raw3359step0 := by
      have heq : raw3359step0 = -raw3359 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3359).symm
    injectiveMoment H raw3359step0 = injectiveMoment H raw3359step1 := by
      have heq : raw3359step1 = (fun i j => raw3359step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3359step0 permutation25 permutation15
    _ = injectiveMoment H node1164 := by rfl

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

theorem canonical3362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3362 = injectiveMoment H node1477 := by
  calc
    injectiveMoment H raw3362 = injectiveMoment H raw3362step0 := by
      have heq : raw3362step0 = -raw3362 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3362).symm
    injectiveMoment H raw3362step0 = injectiveMoment H raw3362step1 := by
      have heq : raw3362step1 = (fun i j => raw3362step0 (permutation85 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3362step0 permutation85 permutation17
    _ = injectiveMoment H node1477 := by rfl

theorem canonical3365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3365 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw3365 = injectiveMoment H raw3365step0 := by
      have heq : raw3365step0 = -raw3365 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3365).symm
    injectiveMoment H raw3365step0 = injectiveMoment H raw3365step1 := by
      have heq : raw3365step1 = (fun i j => raw3365step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3365step0 permutation31 permutation15
    _ = injectiveMoment H node1155 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical3437 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3437 = injectiveMoment H node2687 := by
  calc
    injectiveMoment H raw3437 = injectiveMoment H raw3437step0 := by
      have heq : raw3437step0 = -raw3437 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3437).symm
    injectiveMoment H raw3437step0 = injectiveMoment H raw3437step1 := by
      have heq : raw3437step1 = (fun i j => raw3437step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3437step0 permutation100 permutation15
    _ = injectiveMoment H node2687 := by rfl

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

theorem canonical3630 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3630 = injectiveMoment H node580 := by
  calc
    injectiveMoment H raw3630 = injectiveMoment H raw3630step0 := by
      have heq : raw3630step0 = raw3630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3630).symm
    injectiveMoment H raw3630step0 = injectiveMoment H raw3630step1 := by
      have heq : raw3630step1 = -raw3630step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3630step0).symm
    injectiveMoment H raw3630step1 = injectiveMoment H raw3630step2 := by
      have heq : raw3630step2 = (fun i j => raw3630step1 (permutation30 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3630step1 permutation30 permutation13
    _ = injectiveMoment H node580 := by rfl

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4449 = injectiveMoment H node2203 := by
  rfl

theorem canonical4450 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4450 = injectiveMoment H node578 := by
  calc
    injectiveMoment H raw4450 = injectiveMoment H raw4450step0 := by
      have heq : raw4450step0 = raw4450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4450).symm
    injectiveMoment H raw4450step0 = injectiveMoment H raw4450step1 := by
      have heq : raw4450step1 = -raw4450step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4450step0).symm
    injectiveMoment H raw4450step1 = injectiveMoment H raw4450step2 := by
      have heq : raw4450step2 = (fun i j => raw4450step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4450step1 permutation27 permutation19
    _ = injectiveMoment H node578 := by rfl

theorem canonical4453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4453 = injectiveMoment H node940 := by
  calc
    injectiveMoment H raw4453 = injectiveMoment H raw4453step0 := by
      have heq : raw4453step0 = raw4453.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4453).symm
    injectiveMoment H raw4453step0 = injectiveMoment H raw4453step1 := by
      have heq : raw4453step1 = (fun i j => raw4453step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4453step0 permutation24 permutation29
    _ = injectiveMoment H node940 := by rfl

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

theorem canonical4632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4632 = injectiveMoment H node927 := by
  calc
    injectiveMoment H raw4632 = injectiveMoment H raw4632step0 := by
      have heq : raw4632step0 = raw4632.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4632).symm
    injectiveMoment H raw4632step0 = injectiveMoment H raw4632step1 := by
      have heq : raw4632step1 = (fun i j => raw4632step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4632step0 permutation24 permutation29
    _ = injectiveMoment H node927 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
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

theorem canonical5631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5631 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw5631 = injectiveMoment H raw5631step0 := by
      have heq : raw5631step0 = raw5631.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5631).symm
    injectiveMoment H raw5631step0 = injectiveMoment H raw5631step1 := by
      have heq : raw5631step1 = (fun i j => raw5631step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5631step0 permutation28 permutation6
    _ = injectiveMoment H node150 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5727 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw5727 = injectiveMoment H raw5727step0 := by
      have heq : raw5727step0 = raw5727.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5727).symm
    injectiveMoment H raw5727step0 = injectiveMoment H raw5727step1 := by
      have heq : raw5727step1 = (fun i j => raw5727step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5727step0 permutation23 permutation7
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical5809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5809 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw5809 = injectiveMoment H raw5809step0 := by
      have heq : raw5809step0 = raw5809.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5809).symm
    injectiveMoment H raw5809step0 = injectiveMoment H raw5809step1 := by
      have heq : raw5809step1 = (fun i j => raw5809step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5809step0 permutation12 permutation5
    _ = injectiveMoment H node85 := by rfl

theorem canonical5812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5812 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw5812 = injectiveMoment H raw5812step0 := by
      have heq : raw5812step0 = raw5812.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5812).symm
    injectiveMoment H raw5812step0 = injectiveMoment H raw5812step1 := by
      have heq : raw5812step1 = -raw5812step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5812step0).symm
    injectiveMoment H raw5812step1 = injectiveMoment H raw5812step2 := by
      have heq : raw5812step2 = (fun i j => raw5812step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5812step1 permutation25 permutation3
    _ = injectiveMoment H node132 := by rfl

theorem canonical5818 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5818 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw5818 = injectiveMoment H raw5818step0 := by
      have heq : raw5818step0 = raw5818.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5818).symm
    injectiveMoment H raw5818step0 = injectiveMoment H raw5818step1 := by
      have heq : raw5818step1 = -raw5818step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5818step0).symm
    injectiveMoment H raw5818step1 = injectiveMoment H raw5818step2 := by
      have heq : raw5818step2 = (fun i j => raw5818step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5818step1 permutation25 permutation3
    _ = injectiveMoment H node134 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6036 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw6036 = injectiveMoment H raw6036step0 := by
      have heq : raw6036step0 = (fun i j => raw6036 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6036 permutation11 permutation11
    _ = injectiveMoment H node771 := by rfl

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

theorem canonical6090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6090 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw6090 = injectiveMoment H raw6090step0 := by
      have heq : raw6090step0 = (fun i j => raw6090 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6090 permutation11 permutation11
    _ = injectiveMoment H node775 := by rfl

theorem canonical6091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6091 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw6091 = injectiveMoment H raw6091step0 := by
      have heq : raw6091step0 = raw6091.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6091).symm
    injectiveMoment H raw6091step0 = injectiveMoment H raw6091step1 := by
      have heq : raw6091step1 = (fun i j => raw6091step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6091step0 permutation27 permutation6
    _ = injectiveMoment H node145 := by rfl

theorem canonical6110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6110 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6110 = injectiveMoment H raw6110step0 := by
      have heq : raw6110step0 = raw6110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6110).symm
    injectiveMoment H raw6110step0 = injectiveMoment H raw6110step1 := by
      have heq : raw6110step1 = (fun i j => raw6110step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6110step0 permutation27 permutation6
    _ = injectiveMoment H node150 := by rfl

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

theorem canonical6113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6113 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw6113 = injectiveMoment H raw6113step0 := by
      have heq : raw6113step0 = raw6113.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6113).symm
    injectiveMoment H raw6113step0 = injectiveMoment H raw6113step1 := by
      have heq : raw6113step1 = (fun i j => raw6113step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6113step0 permutation28 permutation6
    _ = injectiveMoment H node146 := by rfl

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

theorem canonical6329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6329 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6329 = injectiveMoment H raw6329step0 := by
      have heq : raw6329step0 = raw6329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6329).symm
    injectiveMoment H raw6329step0 = injectiveMoment H raw6329step1 := by
      have heq : raw6329step1 = (fun i j => raw6329step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6329step0 permutation23 permutation7
    _ = injectiveMoment H node173 := by rfl

theorem canonical6333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6333 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6333 = injectiveMoment H raw6333step0 := by
      have heq : raw6333step0 = raw6333.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6333).symm
    injectiveMoment H raw6333step0 = injectiveMoment H raw6333step1 := by
      have heq : raw6333step1 = -raw6333step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6333step0).symm
    injectiveMoment H raw6333step1 = injectiveMoment H raw6333step2 := by
      have heq : raw6333step2 = (fun i j => raw6333step1 (permutation27 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6333step1 permutation27 permutation7
    _ = injectiveMoment H node244 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6392 = injectiveMoment H node996 := by
  rfl

theorem canonical6397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6397 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw6397 = injectiveMoment H raw6397step0 := by
      have heq : raw6397step0 = raw6397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6397).symm
    injectiveMoment H raw6397step0 = injectiveMoment H raw6397step1 := by
      have heq : raw6397step1 = -raw6397step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6397step0).symm
    injectiveMoment H raw6397step1 = injectiveMoment H raw6397step2 := by
      have heq : raw6397step2 = (fun i j => raw6397step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6397step1 permutation31 permutation3
    _ = injectiveMoment H node150 := by rfl

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

theorem canonical6588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6588 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6588 = injectiveMoment H raw6588step0 := by
      have heq : raw6588step0 = raw6588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6588).symm
    injectiveMoment H raw6588step0 = injectiveMoment H raw6588step1 := by
      have heq : raw6588step1 = -raw6588step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6588step0).symm
    injectiveMoment H raw6588step1 = injectiveMoment H raw6588step2 := by
      have heq : raw6588step2 = (fun i j => raw6588step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6588step1 permutation25 permutation3
    _ = injectiveMoment H node244 := by rfl

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

theorem canonical6628 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6628 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw6628 = injectiveMoment H raw6628step0 := by
      have heq : raw6628step0 = raw6628.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6628).symm
    injectiveMoment H raw6628step0 = injectiveMoment H raw6628step1 := by
      have heq : raw6628step1 = -raw6628step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6628step0).symm
    injectiveMoment H raw6628step1 = injectiveMoment H raw6628step2 := by
      have heq : raw6628step2 = (fun i j => raw6628step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6628step1 permutation25 permutation3
    _ = injectiveMoment H node246 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6941 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6941 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw6941 = injectiveMoment H raw6941step0 := by
      have heq : raw6941step0 = raw6941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6941).symm
    injectiveMoment H raw6941step0 = injectiveMoment H raw6941step1 := by
      have heq : raw6941step1 = -raw6941step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6941step0).symm
    injectiveMoment H raw6941step1 = injectiveMoment H raw6941step2 := by
      have heq : raw6941step2 = (fun i j => raw6941step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6941step1 permutation25 permutation3
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical6947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6947 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw6947 = injectiveMoment H raw6947step0 := by
      have heq : raw6947step0 = raw6947.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6947).symm
    injectiveMoment H raw6947step0 = injectiveMoment H raw6947step1 := by
      have heq : raw6947step1 = -raw6947step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6947step0).symm
    injectiveMoment H raw6947step1 = injectiveMoment H raw6947step2 := by
      have heq : raw6947step2 = (fun i j => raw6947step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6947step1 permutation25 permutation3
    _ = injectiveMoment H node206 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6986 = injectiveMoment H node1164 := by
  rfl

theorem canonical6994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6994 = injectiveMoment H node1168 := by
  rfl

theorem canonical6995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6995 = injectiveMoment H node1169 := by
  rfl

theorem canonical7003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7003 = injectiveMoment H node1175 := by
  rfl

theorem canonical7004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7004 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw7004 = injectiveMoment H raw7004step0 := by
      have heq : raw7004step0 = raw7004.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7004).symm
    injectiveMoment H raw7004step0 = injectiveMoment H raw7004step1 := by
      have heq : raw7004step1 = (fun i j => raw7004step0 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7004step0 permutation32 permutation8
    _ = injectiveMoment H node155 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7019 = injectiveMoment H node1178 := by
  rfl

theorem canonical7020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7020 = injectiveMoment H node1180 := by
  rfl

theorem canonical7021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7021 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw7021 = injectiveMoment H raw7021step0 := by
      have hz : ∀ i, raw7021 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7021step0 = (fun i j => raw7021 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7021 permutation15 hz
    _ = injectiveMoment H node52 := by rfl

theorem canonical7033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7033 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7033 = injectiveMoment H raw7033step0 := by
      have heq : raw7033step0 = raw7033.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7033).symm
    injectiveMoment H raw7033step0 = injectiveMoment H raw7033step1 := by
      have heq : raw7033step1 = (fun i j => raw7033step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7033step0 permutation27 permutation6
    _ = injectiveMoment H node149 := by rfl

theorem canonical7037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7037 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw7037 = injectiveMoment H raw7037step0 := by
      have heq : raw7037step0 = raw7037.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7037).symm
    injectiveMoment H raw7037step0 = injectiveMoment H raw7037step1 := by
      have heq : raw7037step1 = (fun i j => raw7037step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7037step0 permutation28 permutation6
    _ = injectiveMoment H node147 := by rfl

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

theorem canonical7040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7040 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw7040 = injectiveMoment H raw7040step0 := by
      have heq : raw7040step0 = raw7040.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7040).symm
    injectiveMoment H raw7040step0 = injectiveMoment H raw7040step1 := by
      have heq : raw7040step1 = (fun i j => raw7040step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7040step0 permutation28 permutation8
    _ = injectiveMoment H node147 := by rfl

theorem canonical7041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7041 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7041 = injectiveMoment H raw7041step0 := by
      have heq : raw7041step0 = raw7041.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7041).symm
    injectiveMoment H raw7041step0 = injectiveMoment H raw7041step1 := by
      have heq : raw7041step1 = (fun i j => raw7041step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7041step0 permutation27 permutation8
    _ = injectiveMoment H node149 := by rfl

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

theorem canonical7169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7169 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw7169 = injectiveMoment H raw7169step0 := by
      have heq : raw7169step0 = -raw7169 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7169).symm
    injectiveMoment H raw7169step0 = injectiveMoment H raw7169step1 := by
      have heq : raw7169step1 = (fun i j => raw7169step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7169step0 permutation25 permutation15
    _ = injectiveMoment H node1168 := by rfl

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

theorem canonical7519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7519 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7519 = injectiveMoment H raw7519step0 := by
      have heq : raw7519step0 = raw7519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7519).symm
    injectiveMoment H raw7519step0 = injectiveMoment H raw7519step1 := by
      have heq : raw7519step1 = -raw7519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7519step0).symm
    injectiveMoment H raw7519step1 = injectiveMoment H raw7519step2 := by
      have heq : raw7519step2 = (fun i j => raw7519step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7519step1 permutation24 permutation3
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical8223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8223 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw8223 = injectiveMoment H raw8223step0 := by
      have heq : raw8223step0 = raw8223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8223).symm
    injectiveMoment H raw8223step0 = injectiveMoment H raw8223step1 := by
      have heq : raw8223step1 = (fun i j => raw8223step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8223step0 permutation19 permutation4
    _ = injectiveMoment H node199 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8228 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw8228 = injectiveMoment H raw8228step0 := by
      have heq : raw8228step0 = raw8228.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8228).symm
    injectiveMoment H raw8228step0 = injectiveMoment H raw8228step1 := by
      have heq : raw8228step1 = (fun i j => raw8228step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8228step0 permutation19 permutation4
    _ = injectiveMoment H node204 := by rfl

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

theorem canonical8279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8279 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8279 = injectiveMoment H raw8279step0 := by
      have heq : raw8279step0 = raw8279.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8279).symm
    injectiveMoment H raw8279step0 = injectiveMoment H raw8279step1 := by
      have hz : ∀ j, raw8279step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8279step1 = (fun i j => raw8279step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8279step0 permutation9 hz
    injectiveMoment H raw8279step1 = injectiveMoment H raw8279step2 := by
      have heq : raw8279step2 = (fun i j => raw8279step1 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8279step1 permutation8 permutation8
    _ = injectiveMoment H node32 := by rfl

theorem canonical8286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8286 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8286 = injectiveMoment H raw8286step0 := by
      have hz : ∀ i, raw8286 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8286step0 = (fun i j => raw8286 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8286 permutation9 hz
    _ = injectiveMoment H node52 := by rfl

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

theorem canonical8311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8311 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw8311 = injectiveMoment H raw8311step0 := by
      have heq : raw8311step0 = -raw8311 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8311).symm
    injectiveMoment H raw8311step0 = injectiveMoment H raw8311step1 := by
      have hz : ∀ i, raw8311step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8311step1 = (fun i j => raw8311step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8311step0 permutation9 hz
    injectiveMoment H raw8311step1 = injectiveMoment H raw8311step2 := by
      have heq : raw8311step2 = (fun i j => raw8311step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8311step1 permutation7 permutation3
    _ = injectiveMoment H node35 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9953 = injectiveMoment H node199 := by
  calc
    injectiveMoment H raw9953 = injectiveMoment H raw9953step0 := by
      have heq : raw9953step0 = raw9953.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9953).symm
    injectiveMoment H raw9953step0 = injectiveMoment H raw9953step1 := by
      have heq : raw9953step1 = (fun i j => raw9953step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9953step0 permutation29 permutation4
    _ = injectiveMoment H node199 := by rfl

theorem canonical9957 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9957 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw9957 = injectiveMoment H raw9957step0 := by
      have heq : raw9957step0 = raw9957.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9957).symm
    injectiveMoment H raw9957step0 = injectiveMoment H raw9957step1 := by
      have heq : raw9957step1 = -raw9957step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9957step0).symm
    injectiveMoment H raw9957step1 = injectiveMoment H raw9957step2 := by
      have heq : raw9957step2 = (fun i j => raw9957step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9957step1 permutation23 permutation3
    _ = injectiveMoment H node198 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1099 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw1099 = injectiveMoment H raw1099step0 := by
      have heq : raw1099step0 = raw1099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1099).symm
    injectiveMoment H raw1099step0 = injectiveMoment H raw1099step1 := by
      have heq : raw1099step1 = -raw1099step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1099step0).symm
    injectiveMoment H raw1099step1 = injectiveMoment H raw1099step2 := by
      have heq : raw1099step2 = (fun i j => raw1099step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1099step1 permutation10 permutation24
    _ = injectiveMoment H node1257 := by rfl

theorem canonical1101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1101 = injectiveMoment H node397 := by
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

theorem canonical1151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1151 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw1151 = injectiveMoment H raw1151step0 := by
      have heq : raw1151step0 = -raw1151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1151).symm
    injectiveMoment H raw1151step0 = injectiveMoment H raw1151step1 := by
      have heq : raw1151step1 = (fun i j => raw1151step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1151step0 permutation19 permutation23
    _ = injectiveMoment H node998 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1272 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw1272 = injectiveMoment H raw1272step0 := by
      have heq : raw1272step0 = raw1272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1272).symm
    injectiveMoment H raw1272step0 = injectiveMoment H raw1272step1 := by
      have heq : raw1272step1 = -raw1272step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1272step0).symm
    injectiveMoment H raw1272step1 = injectiveMoment H raw1272step2 := by
      have heq : raw1272step2 = (fun i j => raw1272step1 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1272step1 permutation23 permutation5
    _ = injectiveMoment H node135 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1442 = injectiveMoment H node33 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1641 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1641 = injectiveMoment H raw1641step0 := by
      have heq : raw1641step0 = (fun i j => raw1641 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1641 permutation9 permutation15
    _ = injectiveMoment H node771 := by rfl

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

theorem canonical2206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2206 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw2206 = injectiveMoment H raw2206step0 := by
      have heq : raw2206step0 = raw2206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2206).symm
    injectiveMoment H raw2206step0 = injectiveMoment H raw2206step1 := by
      have heq : raw2206step1 = -raw2206step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2206step0).symm
    injectiveMoment H raw2206step1 = injectiveMoment H raw2206step2 := by
      have heq : raw2206step2 = (fun i j => raw2206step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2206step1 permutation21 permutation5
    _ = injectiveMoment H node85 := by rfl

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

theorem canonical2649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2649 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw2649 = injectiveMoment H raw2649step0 := by
      have heq : raw2649step0 = raw2649.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2649).symm
    injectiveMoment H raw2649step0 = injectiveMoment H raw2649step1 := by
      have heq : raw2649step1 = (fun i j => raw2649step0 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2649step0 permutation18 permutation5
    _ = injectiveMoment H node85 := by rfl

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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound33 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node33 = Sparse.eval value33 (momentVector H) := by
  have hc : momentVector H 82 = injectiveMoment H node33 := rfl
  simp [value33, Sparse.eval, hc]

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

theorem sound85 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node85 = Sparse.eval value85 (momentVector H) := by
  have hc : momentVector H 59 = injectiveMoment H node85 := rfl
  simp [value85, Sparse.eval, hc]

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

theorem sound132 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node132 = Sparse.eval value132 (momentVector H) := by
  have heq : pivotMatrix132 = (fun u v => node132 (pivotPermutation132 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node132 = injectiveMoment H pivotMatrix132 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix132 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix132 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix132 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix132 (0 : Fin 3) = raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical333 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix132 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix132 (1 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix132 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix132 (2 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node132 + (injectiveMoment H (mergeFirst pivotMatrix132 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix132 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix132 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value132, value32, value40, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node134 = Sparse.eval value134 (momentVector H) := by
  have hc : momentVector H 81 = injectiveMoment H node134 := rfl
  simp [value134, Sparse.eval, hc]

theorem sound135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node135 = Sparse.eval value135 (momentVector H) := by
  have hc : momentVector H 306 = injectiveMoment H node135 := rfl
  simp [value135, Sparse.eval, hc]

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

theorem sound147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node147 = Sparse.eval value147 (momentVector H) := by
  have heq : pivotMatrix147 = (fun u v => node147 (pivotPermutation147 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node147 = injectiveMoment H pivotMatrix147 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix147 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix147 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix147 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix147 (1 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (1 : Fin 3) = raw1442 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1442 hH).trans (sound33 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix147 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix147 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node147 + (injectiveMoment H (mergeFirst pivotMatrix147 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix147 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix147 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value147, value32, value33, value37, Sparse.eval] at hc ⊢
  linarith

theorem sound149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node149 = Sparse.eval value149 (momentVector H) := by
  have heq : pivotMatrix149 = (fun u v => node149 (pivotPermutation149 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node149 = injectiveMoment H pivotMatrix149 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix149 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix149 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (0 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (1 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix149 (2 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node149 + (injectiveMoment H (mergeFirst pivotMatrix149 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix149 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value149, value52, value59, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node150 = Sparse.eval value150 (momentVector H) := by
  have heq : pivotMatrix150 = (fun u v => node150 (pivotPermutation150 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node150 = injectiveMoment H pivotMatrix150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix150 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (0 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node150 + (injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value150, value35, value52, value56, Sparse.eval] at hc ⊢
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

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

theorem sound199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node199 = Sparse.eval value199 (momentVector H) := by
  have hc : momentVector H 199 = injectiveMoment H node199 := rfl
  simp [value199, Sparse.eval, hc]

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

theorem sound204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node204 = Sparse.eval value204 (momentVector H) := by
  have heq : pivotMatrix204 = (fun u v => node204 (pivotPermutation204 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node204 = injectiveMoment H pivotMatrix204 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix204 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix204 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (0 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix204 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node204 + (injectiveMoment H (mergeFirst pivotMatrix204 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix204 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value204, value37, value41, Sparse.eval] at hc ⊢
  linarith

theorem sound206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node206 = Sparse.eval value206 (momentVector H) := by
  have heq : pivotMatrix206 = (fun u v => node206 (pivotPermutation206 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node206 = injectiveMoment H pivotMatrix206 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix206 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix206 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (0 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix206 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node206 + (injectiveMoment H (mergeFirst pivotMatrix206 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix206 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value206, value32, value36, value40, Sparse.eval] at hc ⊢
  linarith

theorem sound244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node244 = Sparse.eval value244 (momentVector H) := by
  have heq : pivotMatrix244 = (fun u v => node244 (pivotPermutation244 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node244 = injectiveMoment H pivotMatrix244 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix244 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix244 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix244 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix244 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix244 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix244 (1 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix244 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix244 (2 : Fin 3) = raw5555 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5555 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node244 + (injectiveMoment H (mergeFirst pivotMatrix244 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix244 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix244 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value244, value35, value52, Sparse.eval] at hc ⊢
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

theorem sound771 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node771 = Sparse.eval value771 (momentVector H) := by
  have heq : pivotMatrix771 = (fun u v => node771 (pivotPermutation771 u) v) := by apply Matrix.ext; unfold pivotMatrix771 node771 pivotPermutation771; decide +kernel
  have hmoment : injectiveMoment H node771 = injectiveMoment H pivotMatrix771 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix771 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix771 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) =
      Sparse.eval value145 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (0 : Fin 3) = raw6091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw6091; decide +kernel
    rw [heq]
    exact (canonical6091 hH).trans (sound145 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (1 : Fin 3) = raw5631 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5631; decide +kernel
    rw [heq]
    exact (canonical5631 hH).trans (sound150 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix771 (2 : Fin 3) = raw5615 := by apply Matrix.ext; unfold mergeFirst pivotMatrix771 raw5615; decide +kernel
    rw [heq]
    exact (canonical5615 hH).trans (sound146 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node771 + (injectiveMoment H (mergeFirst pivotMatrix771 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix771 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value771, value145, value146, value150, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound14
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound927 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node927 = Sparse.eval value927 (momentVector H) := by
  have heq : pivotMatrix927 = (fun u v => node927.transpose (pivotPermutation927 u) v) := by apply Matrix.ext; unfold pivotMatrix927 node927 pivotPermutation927; decide +kernel
  have hmoment : injectiveMoment H node927 = injectiveMoment H pivotMatrix927 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix927 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix927 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix927 (0 : Fin 3)) =
      Sparse.eval value135 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (0 : Fin 3) = raw1272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw1272; decide +kernel
    rw [heq]
    exact (canonical1272 hH).trans (sound135 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix927 (1 : Fin 3)) =
      Sparse.eval value132 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (1 : Fin 3) = raw5812 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw5812; decide +kernel
    rw [heq]
    exact (canonical5812 hH).trans (sound132 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix927 (2 : Fin 3)) =
      Sparse.eval value134 (momentVector H) := by
    have heq : mergeFirst pivotMatrix927 (2 : Fin 3) = raw5818 := by apply Matrix.ext; unfold mergeFirst pivotMatrix927 raw5818; decide +kernel
    rw [heq]
    exact (canonical5818 hH).trans (sound134 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node927 + (injectiveMoment H (mergeFirst pivotMatrix927 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix927 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix927 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value927, value132, value134, value135, Sparse.eval] at hc ⊢
  linarith

theorem sound940 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node940 = Sparse.eval value940 (momentVector H) := by
  have heq : pivotMatrix940 = (fun u v => node940 (pivotPermutation940 u) v) := by apply Matrix.ext; unfold pivotMatrix940 node940 pivotPermutation940; decide +kernel
  have hmoment : injectiveMoment H node940 = injectiveMoment H pivotMatrix940 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix940 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix940 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix940 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (0 : Fin 3) = raw5727 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw5727; decide +kernel
    rw [heq]
    exact (canonical5727 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix940 (1 : Fin 3)) =
      Sparse.eval value173 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (1 : Fin 3) = raw6329 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw6329; decide +kernel
    rw [heq]
    exact (canonical6329 hH).trans (sound173 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix940 (2 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix940 (2 : Fin 3) = raw6333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix940 raw6333; decide +kernel
    rw [heq]
    exact (canonical6333 hH).trans (sound244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node940 + (injectiveMoment H (mergeFirst pivotMatrix940 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix940 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix940 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value940, value173, value201, value244, Sparse.eval] at hc ⊢
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

theorem sound996 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node996 = Sparse.eval value996 (momentVector H) := by
  have heq : pivotMatrix996 = (fun u v => node996.transpose (pivotPermutation996 u) v) := by apply Matrix.ext; unfold pivotMatrix996 node996 pivotPermutation996; decide +kernel
  have hmoment : injectiveMoment H node996 = injectiveMoment H pivotMatrix996 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix996 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix996 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix996 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (0 : Fin 3) = raw2206 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw2206; decide +kernel
    rw [heq]
    exact (canonical2206 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix996 (1 : Fin 3)) =
      Sparse.eval value244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (1 : Fin 3) = raw6588 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw6588; decide +kernel
    rw [heq]
    exact (canonical6588 hH).trans (sound244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix996 (2 : Fin 3)) =
      Sparse.eval value246 (momentVector H) := by
    have heq : mergeFirst pivotMatrix996 (2 : Fin 3) = raw6628 := by apply Matrix.ext; unfold mergeFirst pivotMatrix996 raw6628; decide +kernel
    rw [heq]
    exact (canonical6628 hH).trans (sound246 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node996 + (injectiveMoment H (mergeFirst pivotMatrix996 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix996 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix996 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value996, value244, value246, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node998 = Sparse.eval value998 (momentVector H) := by
  have heq : pivotMatrix998 = (fun u v => node998 (pivotPermutation998 u) v) := by apply Matrix.ext; unfold pivotMatrix998 node998 pivotPermutation998; decide +kernel
  have hmoment : injectiveMoment H node998 = injectiveMoment H pivotMatrix998 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix998 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix998 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix998 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (0 : Fin 3) = raw8311 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw8311; decide +kernel
    rw [heq]
    exact (canonical8311 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix998 (1 : Fin 3)) =
      Sparse.eval value153 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (1 : Fin 3) = raw6561 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw6561; decide +kernel
    rw [heq]
    exact (canonical6561 hH).trans (sound153 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix998 (2 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix998 (2 : Fin 3) = raw6397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix998 raw6397; decide +kernel
    rw [heq]
    exact (canonical6397 hH).trans (sound150 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node998 + (injectiveMoment H (mergeFirst pivotMatrix998 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix998 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix998 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value998, value150, value153, value35, Sparse.eval] at hc ⊢
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

theorem sound1155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1155 = Sparse.eval value1155 (momentVector H) := by
  have heq : pivotMatrix1155 = (fun u v => node1155.transpose (pivotPermutation1155 u) v) := by apply Matrix.ext; unfold pivotMatrix1155 node1155 pivotPermutation1155; decide +kernel
  have hmoment : injectiveMoment H node1155 = injectiveMoment H pivotMatrix1155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1155 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1155 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1155 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (0 : Fin 3) = raw2649 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw2649; decide +kernel
    rw [heq]
    exact (canonical2649 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1155 (1 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (1 : Fin 3) = raw6941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw6941; decide +kernel
    rw [heq]
    exact (canonical6941 hH).trans (sound201 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1155 (2 : Fin 3)) =
      Sparse.eval value206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1155 (2 : Fin 3) = raw6947 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1155 raw6947; decide +kernel
    rw [heq]
    exact (canonical6947 hH).trans (sound206 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1155 + (injectiveMoment H (mergeFirst pivotMatrix1155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1155, value201, value206, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound1164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1164 = Sparse.eval value1164 (momentVector H) := by
  have heq : pivotMatrix1164 = (fun u v => node1164.transpose (pivotPermutation1164 u) v) := by apply Matrix.ext; unfold pivotMatrix1164 node1164 pivotPermutation1164; decide +kernel
  have hmoment : injectiveMoment H node1164 = injectiveMoment H pivotMatrix1164 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1164 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1164 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) =
      Sparse.eval value85 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (0 : Fin 3) = raw5809 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw5809; decide +kernel
    rw [heq]
    exact (canonical5809 hH).trans (sound85 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (1 : Fin 3) = raw8223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8223; decide +kernel
    rw [heq]
    exact (canonical8223 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3)) =
      Sparse.eval value204 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1164 (2 : Fin 3) = raw8228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1164 raw8228; decide +kernel
    rw [heq]
    exact (canonical8228 hH).trans (sound204 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1164 + (injectiveMoment H (mergeFirst pivotMatrix1164 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1164 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1164, value199, value204, value85, Sparse.eval] at hc ⊢
  linarith

theorem sound1168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1168 = Sparse.eval value1168 (momentVector H) := by
  have heq : pivotMatrix1168 = (fun u v => node1168 (pivotPermutation1168 u) v) := by apply Matrix.ext; unfold pivotMatrix1168 node1168 pivotPermutation1168; decide +kernel
  have hmoment : injectiveMoment H node1168 = injectiveMoment H pivotMatrix1168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1168 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1168 (0 : Fin 3)) =
      Sparse.eval value150 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (0 : Fin 3) = raw6110 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw6110; decide +kernel
    rw [heq]
    exact (canonical6110 hH).trans (sound150 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1168 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (1 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1168 (2 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1168 (2 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1168 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1168 + (injectiveMoment H (mergeFirst pivotMatrix1168 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1168 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1168 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1168, value149, value150, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound1169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1169 = Sparse.eval value1169 (momentVector H) := by
  have heq : pivotMatrix1169 = (fun u v => node1169 (pivotPermutation1169 u) v) := by apply Matrix.ext; unfold pivotMatrix1169 node1169 pivotPermutation1169; decide +kernel
  have hmoment : injectiveMoment H node1169 = injectiveMoment H pivotMatrix1169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1169 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1169 (0 : Fin 3)) =
      Sparse.eval value146 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (0 : Fin 3) = raw6113 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw6113; decide +kernel
    rw [heq]
    exact (canonical6113 hH).trans (sound146 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1169 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (1 : Fin 3) = raw7033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw7033; decide +kernel
    rw [heq]
    exact (canonical7033 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1169 (2 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1169 (2 : Fin 3) = raw7037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1169 raw7037; decide +kernel
    rw [heq]
    exact (canonical7037 hH).trans (sound147 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1169 + (injectiveMoment H (mergeFirst pivotMatrix1169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1169, value146, value147, value149, Sparse.eval] at hc ⊢
  linarith

theorem sound1175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1175 = Sparse.eval value1175 (momentVector H) := by
  have heq : pivotMatrix1175 = (fun u v => node1175 (pivotPermutation1175 u) v) := by apply Matrix.ext; unfold pivotMatrix1175 node1175 pivotPermutation1175; decide +kernel
  have hmoment : injectiveMoment H node1175 = injectiveMoment H pivotMatrix1175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1175 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1175 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1175 (0 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (0 : Fin 3) = raw8279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw8279; decide +kernel
    rw [heq]
    exact (canonical8279 hH).trans (sound32 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1175 (1 : Fin 3)) =
      Sparse.eval value147 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (1 : Fin 3) = raw7040 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw7040; decide +kernel
    rw [heq]
    exact (canonical7040 hH).trans (sound147 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1175 (2 : Fin 3)) =
      Sparse.eval value155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1175 (2 : Fin 3) = raw7004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1175 raw7004; decide +kernel
    rw [heq]
    exact (canonical7004 hH).trans (sound155 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1175 + (injectiveMoment H (mergeFirst pivotMatrix1175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1175, value147, value155, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound1178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1178 = Sparse.eval value1178 (momentVector H) := by
  have heq : pivotMatrix1178 = (fun u v => node1178 (pivotPermutation1178 u) v) := by apply Matrix.ext; unfold pivotMatrix1178 node1178 pivotPermutation1178; decide +kernel
  have hmoment : injectiveMoment H node1178 = injectiveMoment H pivotMatrix1178 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1178 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1178 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (0 : Fin 3) = raw8286 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw8286; decide +kernel
    rw [heq]
    exact (canonical8286 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) =
      Sparse.eval value149 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (1 : Fin 3) = raw7041 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7041; decide +kernel
    rw [heq]
    exact (canonical7041 hH).trans (sound149 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1178 (2 : Fin 3) = raw7021 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1178 raw7021; decide +kernel
    rw [heq]
    exact (canonical7021 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1178 + (injectiveMoment H (mergeFirst pivotMatrix1178 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1178 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1178, value149, value52, Sparse.eval] at hc ⊢
  linarith

theorem sound1180 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1180 = Sparse.eval value1180 (momentVector H) := by
  have heq : pivotMatrix1180 = (fun u v => node1180.transpose (pivotPermutation1180 u) v) := by apply Matrix.ext; unfold pivotMatrix1180 node1180 pivotPermutation1180; decide +kernel
  have hmoment : injectiveMoment H node1180 = injectiveMoment H pivotMatrix1180 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix1180 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1180 3 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) =
      Sparse.eval value201 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (0 : Fin 3) = raw7519 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw7519; decide +kernel
    rw [heq]
    exact (canonical7519 hH).trans (sound201 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) =
      Sparse.eval value199 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (1 : Fin 3) = raw9953 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9953; decide +kernel
    rw [heq]
    exact (canonical9953 hH).trans (sound199 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1180 (2 : Fin 3) = raw9957 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1180 raw9957; decide +kernel
    rw [heq]
    exact (canonical9957 hH).trans (sound198 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1180 + (injectiveMoment H (mergeFirst pivotMatrix1180 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1180 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1180, value198, value199, value201, Sparse.eval] at hc ⊢
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

theorem sound397 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node397 = Sparse.eval value397 (momentVector H) := by
  have hc : momentVector H 74 = injectiveMoment H node397 := rfl
  simp [value397, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound23
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1477 = Sparse.eval value1477 (momentVector H) := by
  have heq : pivotMatrix1477 = (fun u v => node1477 (pivotPermutation1477 u) v) := by apply Matrix.ext; unfold pivotMatrix1477 node1477 pivotPermutation1477; decide +kernel
  have hmoment : injectiveMoment H node1477 = injectiveMoment H pivotMatrix1477 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1477 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1477 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1477 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (0 : Fin 4) = raw1641 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1641; decide +kernel
    rw [heq]
    exact (canonical1641 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1477 (1 : Fin 4)) =
      Sparse.eval value998 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (1 : Fin 4) = raw1151 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1151; decide +kernel
    rw [heq]
    exact (canonical1151 hH).trans (sound998 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1477 (2 : Fin 4)) =
      Sparse.eval value397 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (2 : Fin 4) = raw1101 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1101; decide +kernel
    rw [heq]
    exact (canonical1101 hH).trans (sound397 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1477 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1477 (3 : Fin 4) = raw1099 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1477 raw1099; decide +kernel
    rw [heq]
    exact (canonical1099 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1477 + (injectiveMoment H (mergeFirst pivotMatrix1477 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1477 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1477, value1257, value397, value771, value998, Sparse.eval] at hc ⊢
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

theorem sound578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node578 = Sparse.eval value578 (momentVector H) := by
  have hc : momentVector H 500 = injectiveMoment H node578 := rfl
  simp [value578, Sparse.eval, hc]

theorem sound580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node580 = Sparse.eval value580 (momentVector H) := by
  have hc : momentVector H 502 = injectiveMoment H node580 := rfl
  simp [value580, Sparse.eval, hc]

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

theorem sound2005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2005 = Sparse.eval value2005 (momentVector H) := by
  have heq : pivotMatrix2005 = (fun u v => node2005 (pivotPermutation2005 u) v) := by apply Matrix.ext; unfold pivotMatrix2005 node2005 pivotPermutation2005; decide +kernel
  have hmoment : injectiveMoment H node2005 = injectiveMoment H pivotMatrix2005 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2005 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2005 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2005 (0 : Fin 4)) =
      Sparse.eval value996 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (0 : Fin 4) = raw6392 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw6392; decide +kernel
    rw [heq]
    exact (canonical6392 hH).trans (sound996 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2005 (1 : Fin 4)) =
      Sparse.eval value580 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (1 : Fin 4) = raw3630 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3630; decide +kernel
    rw [heq]
    exact (canonical3630 hH).trans (sound580 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2005 (2 : Fin 4)) =
      Sparse.eval value1155 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (2 : Fin 4) = raw3365 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3365; decide +kernel
    rw [heq]
    exact (canonical3365 hH).trans (sound1155 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2005 (3 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2005 (3 : Fin 4) = raw3359 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2005 raw3359; decide +kernel
    rw [heq]
    exact (canonical3359 hH).trans (sound1164 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2005 + (injectiveMoment H (mergeFirst pivotMatrix2005 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2005 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2005, value1155, value1164, value580, value996, Sparse.eval] at hc ⊢
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

theorem sound2203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2203 = Sparse.eval value2203 (momentVector H) := by
  have heq : pivotMatrix2203 = (fun u v => node2203 (pivotPermutation2203 u) v) := by apply Matrix.ext; unfold pivotMatrix2203 node2203 pivotPermutation2203; decide +kernel
  have hmoment : injectiveMoment H node2203 = injectiveMoment H pivotMatrix2203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2203 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2203 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2203 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (0 : Fin 4) = raw7169 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw7169; decide +kernel
    rw [heq]
    exact (canonical7169 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2203 (1 : Fin 4)) =
      Sparse.eval value927 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (1 : Fin 4) = raw4632 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4632; decide +kernel
    rw [heq]
    exact (canonical4632 hH).trans (sound927 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2203 (2 : Fin 4)) =
      Sparse.eval value940 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (2 : Fin 4) = raw4453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4453; decide +kernel
    rw [heq]
    exact (canonical4453 hH).trans (sound940 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2203 (3 : Fin 4)) =
      Sparse.eval value578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2203 (3 : Fin 4) = raw4450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2203 raw4450; decide +kernel
    rw [heq]
    exact (canonical4450 hH).trans (sound578 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2203 + (injectiveMoment H (mergeFirst pivotMatrix2203 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2203 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2203, value1168, value578, value927, value940, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound41
attribute [-simp] _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2683 = Sparse.eval value2683 (momentVector H) := by
  have heq : pivotMatrix2683 = (fun u v => node2683 (pivotPermutation2683 u) v) := by apply Matrix.ext; unfold pivotMatrix2683 node2683 pivotPermutation2683; decide +kernel
  have hmoment : injectiveMoment H node2683 = injectiveMoment H pivotMatrix2683 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2683 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2683 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2683 (0 : Fin 4)) =
      Sparse.eval value771 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (0 : Fin 4) = raw6036 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6036; decide +kernel
    rw [heq]
    exact (canonical6036 hH).trans (sound771 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2683 (1 : Fin 4)) =
      Sparse.eval value1164 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (1 : Fin 4) = raw6986 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6986; decide +kernel
    rw [heq]
    exact (canonical6986 hH).trans (sound1164 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2683 (2 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (2 : Fin 4) = raw6994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6994; decide +kernel
    rw [heq]
    exact (canonical6994 hH).trans (sound1168 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2683 (3 : Fin 4)) =
      Sparse.eval value1169 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2683 (3 : Fin 4) = raw6995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2683 raw6995; decide +kernel
    rw [heq]
    exact (canonical6995 hH).trans (sound1169 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2683 + (injectiveMoment H (mergeFirst pivotMatrix2683 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2683 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2683, value1164, value1168, value1169, value771, Sparse.eval] at hc ⊢
  linarith

theorem sound2687 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2687 = Sparse.eval value2687 (momentVector H) := by
  have heq : pivotMatrix2687 = (fun u v => node2687 (pivotPermutation2687 u) v) := by apply Matrix.ext; unfold pivotMatrix2687 node2687 pivotPermutation2687; decide +kernel
  have hmoment : injectiveMoment H node2687 = injectiveMoment H pivotMatrix2687 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2687 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2687 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2687 (0 : Fin 4)) =
      Sparse.eval value775 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (0 : Fin 4) = raw6090 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw6090; decide +kernel
    rw [heq]
    exact (canonical6090 hH).trans (sound775 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2687 (1 : Fin 4)) =
      Sparse.eval value1175 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (1 : Fin 4) = raw7003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7003; decide +kernel
    rw [heq]
    exact (canonical7003 hH).trans (sound1175 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2687 (2 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (2 : Fin 4) = raw7019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7019; decide +kernel
    rw [heq]
    exact (canonical7019 hH).trans (sound1178 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2687 (3 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2687 (3 : Fin 4) = raw7020 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2687 raw7020; decide +kernel
    rw [heq]
    exact (canonical7020 hH).trans (sound1180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2687 + (injectiveMoment H (mergeFirst pivotMatrix2687 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2687 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2687, value1175, value1178, value1180, value775, Sparse.eval] at hc ⊢
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

theorem sound3160_e_oai {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3160 = Sparse.eval value3160 (momentVector H) := by
  have heq : pivotMatrix3160 = (fun u v => node3160 (pivotPermutation3160 u) v) := by apply Matrix.ext; unfold pivotMatrix3160 node3160 pivotPermutation3160; decide +kernel
  have hmoment : injectiveMoment H node3160 = injectiveMoment H pivotMatrix3160 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3160 0 = Pi.single (1 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3160 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3160 (0 : Fin 5)) =
      Sparse.eval value2203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (0 : Fin 5) = raw4449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw4449; decide +kernel
    rw [heq]
    exact (canonical4449 hH).trans (sound2203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3160 (1 : Fin 5)) =
      Sparse.eval value2687 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (1 : Fin 5) = raw3437 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3437; decide +kernel
    rw [heq]
    exact (canonical3437 hH).trans (sound2687 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3160 (2 : Fin 5)) =
      Sparse.eval value1477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (2 : Fin 5) = raw3362 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3362; decide +kernel
    rw [heq]
    exact (canonical3362 hH).trans (sound1477 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3160 (3 : Fin 5)) =
      Sparse.eval value2683 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (3 : Fin 5) = raw3358 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3358; decide +kernel
    rw [heq]
    exact (canonical3358 hH).trans (sound2683 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3160 (4 : Fin 5)) =
      Sparse.eval value2005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3160 (4 : Fin 5) = raw3357 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3160 raw3357; decide +kernel
    rw [heq]
    exact (canonical3357 hH).trans (sound2005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3160 + (injectiveMoment H (mergeFirst pivotMatrix3160 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3160 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3160, value1477, value2005, value2203, value2683, value2687, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSemantics.sound3160_e_oai := @OAI.MUB6.Certificate.PairSemantics.sound3160_e_oai
