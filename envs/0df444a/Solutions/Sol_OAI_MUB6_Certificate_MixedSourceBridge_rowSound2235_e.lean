-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:36:06.598603+00:00
-- url     : https://prove2.me/submissions/ed3ebc3b-cd5c-4bea-86bd-03303f5b348b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1866_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2097_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2666_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem integer_eval_familyPairVector (B : Fin 7 → Basis)
    (v : Integer.Sparse (Fin 909)) :
    Integer.Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Integer.Sparse.eval v (PairSemantics.momentVector H)) := by
  rw [← Integer.Sparse.eval_toRational, eval_familyPairVector]
  simp only [Integer.Sparse.eval_toRational]

theorem pair_row_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (v : Integer.Sparse (Fin 909))
    (h : ∀ H, IsHadamard H → Integer.Sparse.eval v (PairSemantics.momentVector H) = 0) :
    Integer.Sparse.eval v (familyPairVector B) = 0 := by
  rw [integer_eval_familyPairVector]
  unfold familyAverage
  trans average (fun _ : Fin 7 => (0 : ℝ))
  · apply average_congr
    intro r
    trans average (fun _ : Coord => (0 : ℝ))
    · apply average_congr
      intro s
      exact h _ (relativeMatrix_isHadamard B hB r s)
    · exact average_zero
  · exact average_zero

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3964 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw3964 = injectiveMoment H raw3964step0 := by
      have heq : raw3964step0 = (fun i j => raw3964 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3964 permutation83 permutation5
    _ = injectiveMoment H node642 := by rfl

theorem canonical3965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3965 = injectiveMoment H node625 := by
  rfl

theorem canonical3966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3966 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw3966 = injectiveMoment H raw3966step0 := by
      have heq : raw3966step0 = -raw3966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3966).symm
    injectiveMoment H raw3966step0 = injectiveMoment H raw3966step1 := by
      have heq : raw3966step1 = (fun i j => raw3966step0 (permutation59 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3966step0 permutation59 permutation6
    _ = injectiveMoment H node705 := by rfl

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

theorem canonical4034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4034 = injectiveMoment H node197 := by
  rfl

theorem canonical4037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4037 = injectiveMoment H node198 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8211 = injectiveMoment H node2101 := by
  calc
    injectiveMoment H raw8211 = injectiveMoment H raw8211step0 := by
      have heq : raw8211step0 = (fun i j => raw8211 (permutation248 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8211 permutation248 permutation3
    _ = injectiveMoment H node2101 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8688 = injectiveMoment H node705 := by
  calc
    injectiveMoment H raw8688 = injectiveMoment H raw8688step0 := by
      have heq : raw8688step0 = -raw8688 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8688).symm
    injectiveMoment H raw8688step0 = injectiveMoment H raw8688step1 := by
      have hz : ∀ j, raw8688step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw8688step1 = (fun i j => raw8688step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8688step0 permutation202 hz
    injectiveMoment H raw8688step1 = injectiveMoment H raw8688step2 := by
      have heq : raw8688step2 = (fun i j => raw8688step1 (permutation118 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8688step1 permutation118 permutation6
    _ = injectiveMoment H node705 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8741 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8741 = injectiveMoment H node2100 := by
  calc
    injectiveMoment H raw8741 = injectiveMoment H raw8741step0 := by
      have heq : raw8741step0 = -raw8741 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8741).symm
    injectiveMoment H raw8741step0 = injectiveMoment H raw8741step1 := by
      have heq : raw8741step1 = (fun i j => raw8741step0 (permutation244 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8741step0 permutation244 permutation8
    _ = injectiveMoment H node2100 := by rfl

theorem canonical8761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8761 = injectiveMoment H node1866 := by
  calc
    injectiveMoment H raw8761 = injectiveMoment H raw8761step0 := by
      have heq : raw8761step0 = (fun i j => raw8761 (permutation248 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8761 permutation248 permutation3
    _ = injectiveMoment H node1866 := by rfl

theorem canonical8762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8762 = injectiveMoment H node2666 := by
  calc
    injectiveMoment H raw8762 = injectiveMoment H raw8762step0 := by
      have heq : raw8762step0 = (fun i j => raw8762 (permutation316 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8762 permutation316 permutation6
    _ = injectiveMoment H node2666 := by rfl

theorem canonical8763 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8763 = injectiveMoment H node2097 := by
  calc
    injectiveMoment H raw8763 = injectiveMoment H raw8763step0 := by
      have heq : raw8763step0 = -raw8763 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8763).symm
    injectiveMoment H raw8763step0 = injectiveMoment H raw8763step1 := by
      have heq : raw8763step1 = (fun i j => raw8763step0 (permutation356 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8763step0 permutation356 permutation4
    _ = injectiveMoment H node2097 := by rfl

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4079 = injectiveMoment H node203 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4103 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4103 = injectiveMoment H raw4103step0 := by
      have heq : raw4103step0 = -raw4103 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4103).symm
    injectiveMoment H raw4103step0 = injectiveMoment H raw4103step1 := by
      have hz : ∀ j, raw4103step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4103step1 = (fun i j => raw4103step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4103step0 permutation15 hz
    injectiveMoment H raw4103step1 = injectiveMoment H raw4103step2 := by
      have heq : raw4103step2 = (fun i j => raw4103step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4103step1 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

theorem canonical4106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4106 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw4106 = injectiveMoment H raw4106step0 := by
      have heq : raw4106step0 = (fun i j => raw4106 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4106 permutation39 permutation3
    _ = injectiveMoment H node659 := by rfl

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

theorem canonical4128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4128 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4128 = injectiveMoment H raw4128step0 := by
      have hz : ∀ j, raw4128 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4128step0 = (fun i j => raw4128 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4128 permutation104 hz
    _ = injectiveMoment H node210 := by rfl

theorem canonical4129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4129 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw4129 = injectiveMoment H raw4129step0 := by
      have heq : raw4129step0 = (fun i j => raw4129 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4129 permutation37 permutation3
    _ = injectiveMoment H node670 := by rfl

theorem canonical4130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4130 = injectiveMoment H node210 := by
  rfl

theorem canonical4131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4131 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4131 = injectiveMoment H raw4131step0 := by
      have heq : raw4131step0 = (fun i j => raw4131 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4131 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4139 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4139 = injectiveMoment H raw4139step0 := by
      have heq : raw4139step0 = -raw4139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4139).symm
    injectiveMoment H raw4139step0 = injectiveMoment H raw4139step1 := by
      have heq : raw4139step1 = (fun i j => raw4139step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4139step0 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4145 = injectiveMoment H node215 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4891 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw4891 = injectiveMoment H raw4891step0 := by
      have heq : raw4891step0 = (fun i j => raw4891 (permutation102 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4891 permutation102 permutation5
    _ = injectiveMoment H node626 := by rfl

theorem canonical4893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4893 = injectiveMoment H node276 := by
  calc
    injectiveMoment H raw4893 = injectiveMoment H raw4893step0 := by
      have heq : raw4893step0 = (fun i j => raw4893 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4893 permutation19 permutation7
    _ = injectiveMoment H node276 := by rfl

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

theorem canonical4918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4918 = injectiveMoment H node224 := by
  rfl

theorem canonical4922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4922 = injectiveMoment H node226 := by
  rfl

theorem canonical4923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4923 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4923 = injectiveMoment H raw4923step0 := by
      have heq : raw4923step0 = (fun i j => raw4923 (permutation17 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4923 permutation17 permutation5
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

theorem canonical4958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4958 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4958 = injectiveMoment H raw4958step0 := by
      have heq : raw4958step0 = (fun i j => raw4958 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4958 permutation19 permutation7
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5385 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5385 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw5385 = injectiveMoment H raw5385step0 := by
      have heq : raw5385step0 = -raw5385 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5385).symm
    injectiveMoment H raw5385step0 = injectiveMoment H raw5385step1 := by
      have heq : raw5385step1 = (fun i j => raw5385step0 (permutation17 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5385step0 permutation17 permutation7
    _ = injectiveMoment H node203 := by rfl

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

theorem canonical2820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2820 = injectiveMoment H node181 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw839 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw839 = injectiveMoment H raw839step0 := by
      have heq : raw839step0 = (fun i j => raw839 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw839 permutation32 permutation8
    _ = injectiveMoment H node229 := by rfl

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

theorem sound21 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node21 = Sparse.eval value21 (momentVector H) := by
  have hc : momentVector H 34 = injectiveMoment H node21 := rfl
  simp [value21, Sparse.eval, hc]

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

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

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

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
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

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
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

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

theorem sound198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node198 = Sparse.eval value198 (momentVector H) := by
  have hc : momentVector H 54 = injectiveMoment H node198 := rfl
  simp [value198, Sparse.eval, hc]

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

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
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

theorem sound215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node215 = Sparse.eval value215 (momentVector H) := by
  have heq : pivotMatrix215 = (fun u v => node215 (pivotPermutation215 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node215 = injectiveMoment H pivotMatrix215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix215 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix215 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (1 : Fin 3) = raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4161 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node215 + (injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value215, value36, value37, value63, Sparse.eval] at hc ⊢
  linarith

theorem sound224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node224 = Sparse.eval value224 (momentVector H) := by
  have hc : momentVector H 25 = injectiveMoment H node224 := rfl
  simp [value224, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw550 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw550 = injectiveMoment H raw550step0 := by
      have heq : raw550step0 = -raw550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw550).symm
    injectiveMoment H raw550step0 = injectiveMoment H raw550step1 := by
      have heq : raw550step1 = (fun i j => raw550step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw550step0 permutation19 permutation5
    _ = injectiveMoment H node198 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw776 = injectiveMoment H node376 := by
  rfl

theorem canonical778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw778 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw778 = injectiveMoment H raw778step0 := by
      have heq : raw778step0 = (fun i j => raw778 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw778 permutation26 permutation6
    _ = injectiveMoment H node226 := by rfl

theorem canonical786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw786 = injectiveMoment H node110 := by
  rfl

theorem canonical789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw789 = injectiveMoment H node111 := by
  rfl

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

theorem canonical804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw804 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw804 = injectiveMoment H raw804step0 := by
      have heq : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw804 permutation32 permutation7
    _ = injectiveMoment H node109 := by rfl

theorem canonical805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw805 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw805 = injectiveMoment H raw805step0 := by
      have heq : raw805step0 = (fun i j => raw805 (permutation18 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw805 permutation18 permutation6
    _ = injectiveMoment H node229 := by rfl

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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

theorem sound110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node110 = Sparse.eval value110 (momentVector H) := by
  have hc : momentVector H 65 = injectiveMoment H node110 := rfl
  simp [value110, Sparse.eval, hc]

theorem sound111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node111 = Sparse.eval value111 (momentVector H) := by
  have hc : momentVector H 33 = injectiveMoment H node111 := rfl
  simp [value111, Sparse.eval, hc]

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

theorem sound276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node276 = Sparse.eval value276 (momentVector H) := by
  have hc : momentVector H 31 = injectiveMoment H node276 := rfl
  simp [value276, Sparse.eval, hc]

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
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound642 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node642 = Sparse.eval value642 (momentVector H) := by
  have heq : pivotMatrix642 = (fun u v => node642 (pivotPermutation642 u) v) := by apply Matrix.ext; unfold pivotMatrix642 node642 pivotPermutation642; decide +kernel
  have hmoment : injectiveMoment H node642 = injectiveMoment H pivotMatrix642 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix642 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix642 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (0 : Fin 4) = raw4918 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4918; decide +kernel
    rw [heq]
    exact (canonical4918 hH).trans (sound224 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (1 : Fin 4) = raw4079 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4079; decide +kernel
    rw [heq]
    exact (canonical4079 hH).trans (sound203 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (2 : Fin 4) = raw4037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4037; decide +kernel
    rw [heq]
    exact (canonical4037 hH).trans (sound198 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix642 (3 : Fin 4) = raw4034 := by apply Matrix.ext; unfold mergeFirst pivotMatrix642 raw4034; decide +kernel
    rw [heq]
    exact (canonical4034 hH).trans (sound197 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node642 + (injectiveMoment H (mergeFirst pivotMatrix642 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix642 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value642, value197, value198, value203, value224, Sparse.eval] at hc ⊢
  linarith

theorem sound659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node659 = Sparse.eval value659 (momentVector H) := by
  have heq : pivotMatrix659 = (fun u v => node659 (pivotPermutation659 u) v) := by apply Matrix.ext; unfold pivotMatrix659 node659 pivotPermutation659; decide +kernel
  have hmoment : injectiveMoment H node659 = injectiveMoment H pivotMatrix659 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix659 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix659 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix659 (0 : Fin 4)) =
      Sparse.eval value181 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (0 : Fin 4) = raw2820 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw2820; decide +kernel
    rw [heq]
    exact (canonical2820 hH).trans (sound181 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix659 (1 : Fin 4)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (1 : Fin 4) = raw4103 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4103; decide +kernel
    rw [heq]
    exact (canonical4103 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix659 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (2 : Fin 4) = raw4130 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4130; decide +kernel
    rw [heq]
    exact (canonical4130 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix659 (3 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix659 (3 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix659 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node659 + (injectiveMoment H (mergeFirst pivotMatrix659 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix659 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value659, value181, value210, value294, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node670 = Sparse.eval value670 (momentVector H) := by
  have heq : pivotMatrix670 = (fun u v => node670 (pivotPermutation670 u) v) := by apply Matrix.ext; unfold pivotMatrix670 node670 pivotPermutation670; decide +kernel
  have hmoment : injectiveMoment H node670 = injectiveMoment H pivotMatrix670 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix670 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix670 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (0 : Fin 4) = raw4958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4958; decide +kernel
    rw [heq]
    exact (canonical4958 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (1 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (2 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (3 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node670 + (injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value670, value203, value207, value210, value215, Sparse.eval] at hc ⊢
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

theorem sound705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node705 = Sparse.eval value705 (momentVector H) := by
  have heq : pivotMatrix705 = (fun u v => node705 (pivotPermutation705 u) v) := by apply Matrix.ext; unfold pivotMatrix705 node705 pivotPermutation705; decide +kernel
  have hmoment : injectiveMoment H node705 = injectiveMoment H pivotMatrix705 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix705 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix705 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (0 : Fin 4) = raw5385 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw5385; decide +kernel
    rw [heq]
    exact (canonical5385 hH).trans (sound203 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (1 : Fin 4) = raw4946 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4946; decide +kernel
    rw [heq]
    exact (canonical4946 hH).trans (sound230 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (2 : Fin 4) = raw4923 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4923; decide +kernel
    rw [heq]
    exact (canonical4923 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix705 (3 : Fin 4) = raw4922 := by apply Matrix.ext; unfold mergeFirst pivotMatrix705 raw4922; decide +kernel
    rw [heq]
    exact (canonical4922 hH).trans (sound226 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node705 + (injectiveMoment H (mergeFirst pivotMatrix705 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix705 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value705, value203, value210, value226, value230, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node367 = Sparse.eval value367 (momentVector H) := by
  have heq : pivotMatrix367 = (fun u v => node367 (pivotPermutation367 u) v) := by apply Matrix.ext; unfold pivotMatrix367 node367 pivotPermutation367; decide +kernel
  have hmoment : injectiveMoment H node367 = injectiveMoment H pivotMatrix367 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix367 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix367 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix367 (0 : Fin 4)) =
      Sparse.eval value198 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (0 : Fin 4) = raw550 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw550; decide +kernel
    rw [heq]
    exact (canonical550 hH).trans (sound198 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix367 (1 : Fin 4)) =
      Sparse.eval value226 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (1 : Fin 4) = raw778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw778; decide +kernel
    rw [heq]
    exact (canonical778 hH).trans (sound226 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix367 (2 : Fin 4)) =
      Sparse.eval value110 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (2 : Fin 4) = raw786 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw786; decide +kernel
    rw [heq]
    exact (canonical786 hH).trans (sound110 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix367 (3 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix367 (3 : Fin 4) = raw789 := by apply Matrix.ext; unfold mergeFirst pivotMatrix367 raw789; decide +kernel
    rw [heq]
    exact (canonical789 hH).trans (sound111 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node367 + (injectiveMoment H (mergeFirst pivotMatrix367 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix367 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value367, value110, value111, value198, value226, Sparse.eval] at hc ⊢
  linarith

theorem sound376 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node376 = Sparse.eval value376 (momentVector H) := by
  have heq : pivotMatrix376 = (fun u v => node376 (pivotPermutation376 u) v) := by apply Matrix.ext; unfold pivotMatrix376 node376 pivotPermutation376; decide +kernel
  have hmoment : injectiveMoment H node376 = injectiveMoment H pivotMatrix376 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix376 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix376 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix376 (0 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (0 : Fin 4) = raw839 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw839; decide +kernel
    rw [heq]
    exact (canonical839 hH).trans (sound229 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix376 (1 : Fin 4)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (1 : Fin 4) = raw808 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw808; decide +kernel
    rw [heq]
    exact (canonical808 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix376 (2 : Fin 4)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (2 : Fin 4) = raw805 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw805; decide +kernel
    rw [heq]
    exact (canonical805 hH).trans (sound229 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix376 (3 : Fin 4)) =
      Sparse.eval value109 (momentVector H) := by
    have heq : mergeFirst pivotMatrix376 (3 : Fin 4) = raw804 := by apply Matrix.ext; unfold mergeFirst pivotMatrix376 raw804; decide +kernel
    rw [heq]
    exact (canonical804 hH).trans (sound109 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node376 + (injectiveMoment H (mergeFirst pivotMatrix376 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix376 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value376, value109, value176, value229, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3974 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw3974 = injectiveMoment H raw3974step0 := by
      have heq : raw3974step0 = -raw3974 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3974).symm
    injectiveMoment H raw3974step0 = injectiveMoment H raw3974step1 := by
      have heq : raw3974step1 = (fun i j => raw3974step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3974step0 permutation41 permutation8
    _ = injectiveMoment H node626 := by rfl

theorem canonical3976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3976 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw3976 = injectiveMoment H raw3976step0 := by
      have heq : raw3976step0 = (fun i j => raw3976 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3976 permutation22 permutation5
    _ = injectiveMoment H node224 := by rfl

theorem canonical3978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3978 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3978 = injectiveMoment H raw3978step0 := by
      have heq : raw3978step0 = -raw3978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3978).symm
    injectiveMoment H raw3978step0 = injectiveMoment H raw3978step1 := by
      have heq : raw3978step1 = (fun i j => raw3978step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3978step0 permutation11 permutation8
    _ = injectiveMoment H node210 := by rfl

theorem canonical3980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3980 = injectiveMoment H node367 := by
  calc
    injectiveMoment H raw3980 = injectiveMoment H raw3980step0 := by
      have heq : raw3980step0 = -raw3980 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3980).symm
    injectiveMoment H raw3980step0 = injectiveMoment H raw3980step1 := by
      have heq : raw3980step1 = (fun i j => raw3980step0 (permutation69 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3980step0 permutation69 permutation5
    _ = injectiveMoment H node367 := by rfl

theorem canonical3985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3985 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw3985 = injectiveMoment H raw3985step0 := by
      have heq : raw3985step0 = -raw3985 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3985).symm
    injectiveMoment H raw3985step0 = injectiveMoment H raw3985step1 := by
      have heq : raw3985step1 = (fun i j => raw3985step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3985step0 permutation16 permutation5
    _ = injectiveMoment H node111 := by rfl

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

theorem sound625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node625 = Sparse.eval value625 (momentVector H) := by
  have hc : momentVector H 195 = injectiveMoment H node625 := rfl
  simp [value625, Sparse.eval, hc]

theorem sound626 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node626 = Sparse.eval value626 (momentVector H) := by
  have heq : pivotMatrix626 = (fun u v => node626 (pivotPermutation626 u) v) := by apply Matrix.ext; unfold pivotMatrix626 node626 pivotPermutation626; decide +kernel
  have hmoment : injectiveMoment H node626 = injectiveMoment H pivotMatrix626 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix626 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix626 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix626 (0 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix626 (0 : Fin 4) = raw4893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix626 raw4893; decide +kernel
    rw [heq]
    exact (canonical4893 hH).trans (sound276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix626 (1 : Fin 4)) =
      Sparse.eval value111 (momentVector H) := by
    have heq : mergeFirst pivotMatrix626 (1 : Fin 4) = raw3985 := by apply Matrix.ext; unfold mergeFirst pivotMatrix626 raw3985; decide +kernel
    rw [heq]
    exact (canonical3985 hH).trans (sound111 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix626 (2 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix626 (2 : Fin 4) = raw3978 := by apply Matrix.ext; unfold mergeFirst pivotMatrix626 raw3978; decide +kernel
    rw [heq]
    exact (canonical3978 hH).trans (sound210 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix626 (3 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix626 (3 : Fin 4) = raw3976 := by apply Matrix.ext; unfold mergeFirst pivotMatrix626 raw3976; decide +kernel
    rw [heq]
    exact (canonical3976 hH).trans (sound224 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node626 + (injectiveMoment H (mergeFirst pivotMatrix626 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix626 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix626 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix626 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value626, value111, value210, value224, value276, Sparse.eval] at hc ⊢
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

theorem sound2100 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2100 = Sparse.eval value2100 (momentVector H) := by
  have heq : pivotMatrix2100 = (fun u v => node2100 (pivotPermutation2100 u) v) := by apply Matrix.ext; unfold pivotMatrix2100 node2100 pivotPermutation2100; decide +kernel
  have hmoment : injectiveMoment H node2100 = injectiveMoment H pivotMatrix2100 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2100 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2100 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2100 (0 : Fin 5)) =
      Sparse.eval value376 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2100 (0 : Fin 5) = raw776 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2100 raw776; decide +kernel
    rw [heq]
    exact (canonical776 hH).trans (sound376 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2100 (1 : Fin 5)) =
      Sparse.eval value626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2100 (1 : Fin 5) = raw3974 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2100 raw3974; decide +kernel
    rw [heq]
    exact (canonical3974 hH).trans (sound626 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2100 (2 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2100 (2 : Fin 5) = raw4106 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2100 raw4106; decide +kernel
    rw [heq]
    exact (canonical4106 hH).trans (sound659 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2100 (3 : Fin 5)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2100 (3 : Fin 5) = raw4128 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2100 raw4128; decide +kernel
    rw [heq]
    exact (canonical4128 hH).trans (sound210 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2100 (4 : Fin 5)) =
      Sparse.eval value670 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2100 (4 : Fin 5) = raw4129 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2100 raw4129; decide +kernel
    rw [heq]
    exact (canonical4129 hH).trans (sound670 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2100 + (injectiveMoment H (mergeFirst pivotMatrix2100 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2100 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2100 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2100 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2100 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2100, value210, value376, value626, value659, value670, Sparse.eval] at hc ⊢
  linarith

theorem sound2101 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2101 = Sparse.eval value2101 (momentVector H) := by
  have heq : pivotMatrix2101 = (fun u v => node2101 (pivotPermutation2101 u) v) := by apply Matrix.ext; unfold pivotMatrix2101 node2101 pivotPermutation2101; decide +kernel
  have hmoment : injectiveMoment H node2101 = injectiveMoment H pivotMatrix2101 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2101 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2101 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2101 (0 : Fin 5)) =
      Sparse.eval value626 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2101 (0 : Fin 5) = raw4891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2101 raw4891; decide +kernel
    rw [heq]
    exact (canonical4891 hH).trans (sound626 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2101 (1 : Fin 5)) =
      Sparse.eval value367 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2101 (1 : Fin 5) = raw3980 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2101 raw3980; decide +kernel
    rw [heq]
    exact (canonical3980 hH).trans (sound367 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2101 (2 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2101 (2 : Fin 5) = raw3966 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2101 raw3966; decide +kernel
    rw [heq]
    exact (canonical3966 hH).trans (sound705 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2101 (3 : Fin 5)) =
      Sparse.eval value625 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2101 (3 : Fin 5) = raw3965 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2101 raw3965; decide +kernel
    rw [heq]
    exact (canonical3965 hH).trans (sound625 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2101 (4 : Fin 5)) =
      Sparse.eval value642 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2101 (4 : Fin 5) = raw3964 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2101 raw3964; decide +kernel
    rw [heq]
    exact (canonical3964 hH).trans (sound642 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2101 + (injectiveMoment H (mergeFirst pivotMatrix2101 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2101 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2101 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2101 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2101 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2101, value367, value625, value626, value642, value705, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem boundarySound74 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow74 (momentVector H) = 0 := by
  have hshape : boundaryMatrix74 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix74 2 1 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix74 (0 : Fin 6)) =
      Sparse.eval value2101 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (0 : Fin 6) = raw8211 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8211 hH).trans (sound2101 hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix74 (1 : Fin 6)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (1 : Fin 6) = raw8688 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8688 hH).trans (sound705 hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix74 (2 : Fin 6)) =
      Sparse.eval value2100 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (2 : Fin 6) = raw8741 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8741 hH).trans (sound2100 hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix74 (3 : Fin 6)) =
      Sparse.eval value1866 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (3 : Fin 6) = raw8761 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8761 hH).trans (sound1866_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix74 (4 : Fin 6)) =
      Sparse.eval value2666 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (4 : Fin 6) = raw8762 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8762 hH).trans (sound2666_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix74 (5 : Fin 6)) =
      Sparse.eval value2097 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix74 (5 : Fin 6) = raw8763 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical8763 hH).trans (sound2097_e hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix74 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix74 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow74, value1866, value2097, value2100, value2101, value2666, value705, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2235 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2235)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow74) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2235_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2235 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2235, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow74 (fun _ hH => PairSemantics.boundarySound74 hH)

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e_oai
