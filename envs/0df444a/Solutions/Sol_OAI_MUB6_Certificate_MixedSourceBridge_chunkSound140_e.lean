-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:10:34.208275+00:00
-- url     : https://prove2.me/submissions/f6b4e952-341f-41b1-bc4c-f4ca94fb9900

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2240_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2241_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2242_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2244_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2245_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2246_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2247_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2248_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2249_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2250_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2251_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2252_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2253_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2254_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2255_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2908_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2910_e
import Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound2914_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3368 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3368 = injectiveMoment H node2908 := by
  calc
    injectiveMoment H raw3368 = injectiveMoment H raw3368step0 := by
      have heq : raw3368step0 = -raw3368 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3368).symm
    injectiveMoment H raw3368step0 = injectiveMoment H raw3368step1 := by
      have heq : raw3368step1 = (fun i j => raw3368step0 (permutation409 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3368step0 permutation409 permutation9
    _ = injectiveMoment H node2908 := by rfl

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

theorem canonical7261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7261 = injectiveMoment H node2910 := by
  calc
    injectiveMoment H raw7261 = injectiveMoment H raw7261step0 := by
      have heq : raw7261step0 = -raw7261 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7261).symm
    injectiveMoment H raw7261step0 = injectiveMoment H raw7261step1 := by
      have heq : raw7261step1 = (fun i j => raw7261step0 (permutation408 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7261step0 permutation408 permutation9
    _ = injectiveMoment H node2910 := by rfl

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

theorem canonical7291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7291 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw7291 = injectiveMoment H raw7291step0 := by
      have heq : raw7291step0 = -raw7291 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7291).symm
    injectiveMoment H raw7291step0 = injectiveMoment H raw7291step1 := by
      have heq : raw7291step1 = (fun i j => raw7291step0 (permutation407 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7291step0 permutation407 permutation9
    _ = injectiveMoment H node2914 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7302 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7302 = injectiveMoment H node2910 := by
  calc
    injectiveMoment H raw7302 = injectiveMoment H raw7302step0 := by
      have heq : raw7302step0 = -raw7302 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7302).symm
    injectiveMoment H raw7302step0 = injectiveMoment H raw7302step1 := by
      have heq : raw7302step1 = (fun i j => raw7302step0 (permutation361 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7302step0 permutation361 permutation11
    _ = injectiveMoment H node2910 := by rfl

theorem canonical7305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7305 = injectiveMoment H node2914 := by
  calc
    injectiveMoment H raw7305 = injectiveMoment H raw7305step0 := by
      have heq : raw7305step0 = -raw7305 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7305).symm
    injectiveMoment H raw7305step0 = injectiveMoment H raw7305step1 := by
      have heq : raw7305step1 = (fun i j => raw7305step0 (permutation359 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7305step0 permutation359 permutation11
    _ = injectiveMoment H node2914 := by rfl

theorem canonical7306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7306 = injectiveMoment H node3373 := by
  calc
    injectiveMoment H raw7306 = injectiveMoment H raw7306step0 := by
      have heq : raw7306step0 = -raw7306 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7306).symm
    injectiveMoment H raw7306step0 = injectiveMoment H raw7306step1 := by
      have heq : raw7306step1 = (fun i j => raw7306step0 (permutation409 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7306step0 permutation409 permutation9
    _ = injectiveMoment H node3373 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8697 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw8697 = injectiveMoment H raw8697step0 := by
      have hz : ∀ j, raw8697 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8697step0 = (fun i j => raw8697 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8697 permutation7 hz
    injectiveMoment H raw8697step0 = injectiveMoment H raw8697step1 := by
      have hz : ∀ i, raw8697step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8697step1 = (fun i j => raw8697step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8697step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem canonical10000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10000 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw10000 = injectiveMoment H raw10000step0 := by
      have hz : ∀ i, raw10000 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw10000step0 = (fun i j => raw10000 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw10000 permutation3 hz
    injectiveMoment H raw10000step0 = injectiveMoment H raw10000step1 := by
      have heq : raw10000step1 = (fun i j => raw10000step0 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10000step0 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7895 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7895 = injectiveMoment H raw7895step0 := by
      have hz : ∀ i, raw7895 i (permutation7 0) = 0 := by decide +kernel
      have heq : raw7895step0 = (fun i j => raw7895 i (permutation7 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7895 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7453 = injectiveMoment H node64 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8542 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8542 = injectiveMoment H raw8542step0 := by
      have heq : raw8542step0 = (fun i j => raw8542 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8542 permutation5 permutation4
    _ = injectiveMoment H node64 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound64 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node64 = Sparse.eval value64 (momentVector H) := by
  have heq : pivotMatrix64 = (fun u v => node64 (pivotPermutation64 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node64 = injectiveMoment H pivotMatrix64 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix64 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix64 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (0 : Fin 2) = raw7895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7895 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (1 : Fin 2) = raw10000 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical10000 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node64 + (injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value64, value5, Sparse.eval] at hc ⊢
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

theorem sound287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node287 = Sparse.eval value287 (momentVector H) := by
  have heq : pivotMatrix287 = (fun u v => node287 (pivotPermutation287 u) v) := by apply Matrix.ext; unfold pivotMatrix287 node287 pivotPermutation287; decide +kernel
  have hmoment : injectiveMoment H node287 = injectiveMoment H pivotMatrix287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix287 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix287 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (0 : Fin 3) = raw7453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw7453; decide +kernel
    rw [heq]
    exact (canonical7453 hH).trans (sound64 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node287 + (injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value287, value61, value62, value64, Sparse.eval] at hc ⊢
  linarith

theorem sound293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node293 = Sparse.eval value293 (momentVector H) := by
  have heq : pivotMatrix293 = (fun u v => node293 (pivotPermutation293 u) v) := by apply Matrix.ext; unfold pivotMatrix293 node293 pivotPermutation293; decide +kernel
  have hmoment : injectiveMoment H node293 = injectiveMoment H pivotMatrix293 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix293 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix293 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (1 : Fin 3) = raw8542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8542; decide +kernel
    rw [heq]
    exact (canonical8542 hH).trans (sound64 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (2 : Fin 3) = raw8697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8697; decide +kernel
    rw [heq]
    exact (canonical8697 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node293 + (injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value293, value5, value61, value64, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5676 = injectiveMoment H node2704 := by
  calc
    injectiveMoment H raw5676 = injectiveMoment H raw5676step0 := by
      have heq : raw5676step0 = (fun i j => raw5676 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5676 permutation41 permutation11
    _ = injectiveMoment H node2704 := by rfl

theorem canonical5680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5680 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw5680 = injectiveMoment H raw5680step0 := by
      have heq : raw5680step0 = raw5680.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5680).symm
    injectiveMoment H raw5680step0 = injectiveMoment H raw5680step1 := by
      have heq : raw5680step1 = (fun i j => raw5680step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5680step0 permutation28 permutation24
    _ = injectiveMoment H node969 := by rfl

theorem canonical5683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5683 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw5683 = injectiveMoment H raw5683step0 := by
      have heq : raw5683step0 = raw5683.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5683).symm
    injectiveMoment H raw5683step0 = injectiveMoment H raw5683step1 := by
      have heq : raw5683step1 = (fun i j => raw5683step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5683step0 permutation30 permutation30
    _ = injectiveMoment H node974 := by rfl

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

theorem canonical6543 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6543 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw6543 = injectiveMoment H raw6543step0 := by
      have hz : ∀ i, raw6543 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw6543step0 = (fun i j => raw6543 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw6543 permutation21 hz
    _ = injectiveMoment H node61 := by rfl

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

theorem canonical6699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6699 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw6699 = injectiveMoment H raw6699step0 := by
      have heq : raw6699step0 = raw6699.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6699).symm
    injectiveMoment H raw6699step0 = injectiveMoment H raw6699step1 := by
      have heq : raw6699step1 = (fun i j => raw6699step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6699step0 permutation25 permutation6
    _ = injectiveMoment H node293 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6486 = injectiveMoment H node1048 := by
  rfl

theorem canonical6494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6494 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6494 = injectiveMoment H raw6494step0 := by
      have heq : raw6494step0 = raw6494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6494).symm
    injectiveMoment H raw6494step0 = injectiveMoment H raw6494step1 := by
      have heq : raw6494step1 = (fun i j => raw6494step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6494step0 permutation27 permutation6
    _ = injectiveMoment H node287 := by rfl

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

theorem canonical8316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8316 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8316 = injectiveMoment H raw8316step0 := by
      have heq : raw8316step0 = -raw8316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8316).symm
    injectiveMoment H raw8316step0 = injectiveMoment H raw8316step1 := by
      have hz : ∀ i, raw8316step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8316step1 = (fun i j => raw8316step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8316step0 permutation9 hz
    injectiveMoment H raw8316step1 = injectiveMoment H raw8316step2 := by
      have heq : raw8316step2 = (fun i j => raw8316step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8316step1 permutation8 permutation3
    _ = injectiveMoment H node44 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6277 = injectiveMoment H node970 := by
  rfl

theorem canonical6280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6280 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6280 = injectiveMoment H raw6280step0 := by
      have heq : raw6280step0 = (fun i j => raw6280 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6280 permutation11 permutation11
    _ = injectiveMoment H node942 := by rfl

theorem canonical6283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6283 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6283 = injectiveMoment H raw6283step0 := by
      have heq : raw6283step0 = raw6283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6283).symm
    injectiveMoment H raw6283step0 = injectiveMoment H raw6283step1 := by
      have heq : raw6283step1 = (fun i j => raw6283step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6283step0 permutation27 permutation6
    _ = injectiveMoment H node271 := by rfl

theorem canonical6287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6287 = injectiveMoment H node974 := by
  rfl

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

theorem canonical6217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6217 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw6217 = injectiveMoment H raw6217step0 := by
      have heq : raw6217step0 = (fun i j => raw6217 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6217 permutation41 permutation11
    _ = injectiveMoment H node2532 := by rfl

theorem canonical6220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6220 = injectiveMoment H node942 := by
  rfl

theorem canonical6223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6223 = injectiveMoment H node945 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7081 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw7081 = injectiveMoment H raw7081step0 := by
      have heq : raw7081step0 = raw7081.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7081).symm
    injectiveMoment H raw7081step0 = injectiveMoment H raw7081step1 := by
      have heq : raw7081step1 = (fun i j => raw7081step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7081step0 permutation32 permutation32
    _ = injectiveMoment H node974 := by rfl

theorem canonical7094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7094 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw7094 = injectiveMoment H raw7094step0 := by
      have hz : ∀ i, raw7094 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7094step0 = (fun i j => raw7094 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7094 permutation15 hz
    _ = injectiveMoment H node271 := by rfl

theorem canonical7097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7097 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw7097 = injectiveMoment H raw7097step0 := by
      have heq : raw7097step0 = raw7097.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7097).symm
    injectiveMoment H raw7097step0 = injectiveMoment H raw7097step1 := by
      have heq : raw7097step1 = (fun i j => raw7097step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7097step0 permutation27 permutation18
    _ = injectiveMoment H node969 := by rfl

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

theorem canonical7181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7181 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw7181 = injectiveMoment H raw7181step0 := by
      have heq : raw7181step0 = raw7181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7181).symm
    injectiveMoment H raw7181step0 = injectiveMoment H raw7181step1 := by
      have heq : raw7181step1 = -raw7181step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7181step0).symm
    injectiveMoment H raw7181step1 = injectiveMoment H raw7181step2 := by
      have heq : raw7181step2 = (fun i j => raw7181step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7181step1 permutation29 permutation4
    _ = injectiveMoment H node230 := by rfl

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

theorem sound942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node942 = Sparse.eval value942 (momentVector H) := by
  have heq : pivotMatrix942 = (fun u v => node942 (pivotPermutation942 u) v) := by apply Matrix.ext; unfold pivotMatrix942 node942 pivotPermutation942; decide +kernel
  have hmoment : injectiveMoment H node942 = injectiveMoment H pivotMatrix942 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix942 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix942 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (0 : Fin 3) = raw7181 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw7181; decide +kernel
    rw [heq]
    exact (canonical7181 hH).trans (sound230 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix942 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix942 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node942 + (injectiveMoment H (mergeFirst pivotMatrix942 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix942 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value942, value176, value229, value230, Sparse.eval] at hc ⊢
  linarith

theorem sound945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node945 = Sparse.eval value945 (momentVector H) := by
  have heq : pivotMatrix945 = (fun u v => node945 (pivotPermutation945 u) v) := by apply Matrix.ext; unfold pivotMatrix945 node945 pivotPermutation945; decide +kernel
  have hmoment : injectiveMoment H node945 = injectiveMoment H pivotMatrix945 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix945 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix945 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (0 : Fin 3) = raw8316 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw8316; decide +kernel
    rw [heq]
    exact (canonical8316 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (1 : Fin 3) = raw6335 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6335; decide +kernel
    rw [heq]
    exact (canonical6335 hH).trans (sound229 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3)) =
      Sparse.eval value229 (momentVector H) := by
    have heq : mergeFirst pivotMatrix945 (2 : Fin 3) = raw6225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix945 raw6225; decide +kernel
    rw [heq]
    exact (canonical6225 hH).trans (sound229 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node945 + (injectiveMoment H (mergeFirst pivotMatrix945 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix945 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value945, value229, value44, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound15
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound966 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node966 = Sparse.eval value966 (momentVector H) := by
  have heq : pivotMatrix966 = (fun u v => node966 (pivotPermutation966 u) v) := by apply Matrix.ext; unfold pivotMatrix966 node966 pivotPermutation966; decide +kernel
  have hmoment : injectiveMoment H node966 = injectiveMoment H pivotMatrix966 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix966 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix966 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix966 (0 : Fin 3)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (0 : Fin 3) = raw6494 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6494; decide +kernel
    rw [heq]
    exact (canonical6494 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix966 (1 : Fin 3)) =
      Sparse.eval value176 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (1 : Fin 3) = raw6292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6292; decide +kernel
    rw [heq]
    exact (canonical6292 hH).trans (sound176 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix966 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix966 (2 : Fin 3) = raw6283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix966 raw6283; decide +kernel
    rw [heq]
    exact (canonical6283 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node966 + (injectiveMoment H (mergeFirst pivotMatrix966 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix966 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix966 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value966, value176, value271, value287, Sparse.eval] at hc ⊢
  linarith

theorem sound969 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node969 = Sparse.eval value969 (momentVector H) := by
  have heq : pivotMatrix969 = (fun u v => node969 (pivotPermutation969 u) v) := by apply Matrix.ext; unfold pivotMatrix969 node969 pivotPermutation969; decide +kernel
  have hmoment : injectiveMoment H node969 = injectiveMoment H pivotMatrix969 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix969 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix969 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix969 (0 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (0 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix969 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (1 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix969 (2 : Fin 3)) =
      Sparse.eval value285 (momentVector H) := by
    have heq : mergeFirst pivotMatrix969 (2 : Fin 3) = raw6315 := by apply Matrix.ext; unfold mergeFirst pivotMatrix969 raw6315; decide +kernel
    rw [heq]
    exact (canonical6315 hH).trans (sound285 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node969 + (injectiveMoment H (mergeFirst pivotMatrix969 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix969 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix969 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value969, value271, value285, value294, Sparse.eval] at hc ⊢
  linarith

theorem sound970 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node970 = Sparse.eval value970 (momentVector H) := by
  have heq : pivotMatrix970 = (fun u v => node970 (pivotPermutation970 u) v) := by apply Matrix.ext; unfold pivotMatrix970 node970 pivotPermutation970; decide +kernel
  have hmoment : injectiveMoment H node970 = injectiveMoment H pivotMatrix970 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix970 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix970 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix970 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (0 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix970 (1 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (1 : Fin 3) = raw6326 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6326; decide +kernel
    rw [heq]
    exact (canonical6326 hH).trans (sound271 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix970 (2 : Fin 3)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix970 (2 : Fin 3) = raw6324 := by apply Matrix.ext; unfold mergeFirst pivotMatrix970 raw6324; decide +kernel
    rw [heq]
    exact (canonical6324 hH).trans (sound271 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node970 + (injectiveMoment H (mergeFirst pivotMatrix970 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix970 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix970 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value970, value271, value61, Sparse.eval] at hc ⊢
  linarith

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

theorem sound1048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1048 = Sparse.eval value1048 (momentVector H) := by
  have heq : pivotMatrix1048 = (fun u v => node1048 (pivotPermutation1048 u) v) := by apply Matrix.ext; unfold pivotMatrix1048 node1048 pivotPermutation1048; decide +kernel
  have hmoment : injectiveMoment H node1048 = injectiveMoment H pivotMatrix1048 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1048 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix1048 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1048 (0 : Fin 3)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (0 : Fin 3) = raw6699 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6699; decide +kernel
    rw [heq]
    exact (canonical6699 hH).trans (sound293 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1048 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (1 : Fin 3) = raw6543 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6543; decide +kernel
    rw [heq]
    exact (canonical6543 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1048 (2 : Fin 3)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1048 (2 : Fin 3) = raw6540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1048 raw6540; decide +kernel
    rw [heq]
    exact (canonical6540 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node1048 + (injectiveMoment H (mergeFirst pivotMatrix1048 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1048 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix1048 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value1048, value293, value294, value61, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6254 = injectiveMoment H node970 := by
  calc
    injectiveMoment H raw6254 = injectiveMoment H raw6254step0 := by
      have hz : ∀ j, raw6254 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw6254step0 = (fun i j => raw6254 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6254 permutation80 hz
    _ = injectiveMoment H node970 := by rfl

theorem canonical6261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6261 = injectiveMoment H node966 := by
  rfl

theorem canonical6265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6265 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6265 = injectiveMoment H raw6265step0 := by
      have heq : raw6265step0 = (fun i j => raw6265 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6265 permutation35 permutation9
    _ = injectiveMoment H node2551 := by rfl

theorem canonical6267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6267 = injectiveMoment H node2531 := by
  calc
    injectiveMoment H raw6267 = injectiveMoment H raw6267step0 := by
      have heq : raw6267step0 = (fun i j => raw6267 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6267 permutation41 permutation11
    _ = injectiveMoment H node2531 := by rfl

theorem canonical6270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6270 = injectiveMoment H node969 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound42
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2704 = Sparse.eval value2704 (momentVector H) := by
  have heq : pivotMatrix2704 = (fun u v => node2704 (pivotPermutation2704 u) v) := by apply Matrix.ext; unfold pivotMatrix2704 node2704 pivotPermutation2704; decide +kernel
  have hmoment : injectiveMoment H node2704 = injectiveMoment H pivotMatrix2704 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2704 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2704 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2704 (0 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (0 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2704 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (1 : Fin 4) = raw7081 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7081; decide +kernel
    rw [heq]
    exact (canonical7081 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2704 (2 : Fin 4)) =
      Sparse.eval value271 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (2 : Fin 4) = raw7094 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7094; decide +kernel
    rw [heq]
    exact (canonical7094 hH).trans (sound271 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2704 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2704 (3 : Fin 4) = raw7097 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2704 raw7097; decide +kernel
    rw [heq]
    exact (canonical7097 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2704 + (injectiveMoment H (mergeFirst pivotMatrix2704 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2704 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2704, value271, value969, value970, value974, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound39
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2531 = Sparse.eval value2531 (momentVector H) := by
  have heq : pivotMatrix2531 = (fun u v => node2531 (pivotPermutation2531 u) v) := by apply Matrix.ext; unfold pivotMatrix2531 node2531 pivotPermutation2531; decide +kernel
  have hmoment : injectiveMoment H node2531 = injectiveMoment H pivotMatrix2531 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2531 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2531 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2531 (0 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (0 : Fin 4) = raw5680 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw5680; decide +kernel
    rw [heq]
    exact (canonical5680 hH).trans (sound969 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2531 (1 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (1 : Fin 4) = raw6220 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6220; decide +kernel
    rw [heq]
    exact (canonical6220 hH).trans (sound942 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2531 (2 : Fin 4)) =
      Sparse.eval value966 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (2 : Fin 4) = raw6261 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6261; decide +kernel
    rw [heq]
    exact (canonical6261 hH).trans (sound966 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2531 (3 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2531 (3 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2531 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2531 + (injectiveMoment H (mergeFirst pivotMatrix2531 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2531 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2531, value942, value966, value969, value970, Sparse.eval] at hc ⊢
  linarith

theorem sound2532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2532 = Sparse.eval value2532 (momentVector H) := by
  have heq : pivotMatrix2532 = (fun u v => node2532 (pivotPermutation2532 u) v) := by apply Matrix.ext; unfold pivotMatrix2532 node2532 pivotPermutation2532; decide +kernel
  have hmoment : injectiveMoment H node2532 = injectiveMoment H pivotMatrix2532 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2532 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2532 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2532 (0 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (0 : Fin 4) = raw5683 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw5683; decide +kernel
    rw [heq]
    exact (canonical5683 hH).trans (sound974 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2532 (1 : Fin 4)) =
      Sparse.eval value945 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (1 : Fin 4) = raw6223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6223; decide +kernel
    rw [heq]
    exact (canonical6223 hH).trans (sound945 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2532 (2 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (2 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2532 (3 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2532 (3 : Fin 4) = raw6280 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2532 raw6280; decide +kernel
    rw [heq]
    exact (canonical6280 hH).trans (sound942 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2532 + (injectiveMoment H (mergeFirst pivotMatrix2532 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2532 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2532, value942, value945, value970, value974, Sparse.eval] at hc ⊢
  linarith

theorem sound2551 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2551 = Sparse.eval value2551 (momentVector H) := by
  have heq : pivotMatrix2551 = (fun u v => node2551 (pivotPermutation2551 u) v) := by apply Matrix.ext; unfold pivotMatrix2551 node2551 pivotPermutation2551; decide +kernel
  have hmoment : injectiveMoment H node2551 = injectiveMoment H pivotMatrix2551 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2551 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2551 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2551 (0 : Fin 4)) =
      Sparse.eval value1048 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (0 : Fin 4) = raw6486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6486; decide +kernel
    rw [heq]
    exact (canonical6486 hH).trans (sound1048 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2551 (1 : Fin 4)) =
      Sparse.eval value974 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (1 : Fin 4) = raw6287 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6287; decide +kernel
    rw [heq]
    exact (canonical6287 hH).trans (sound974 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2551 (2 : Fin 4)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (2 : Fin 4) = raw6277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6277; decide +kernel
    rw [heq]
    exact (canonical6277 hH).trans (sound970 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2551 (3 : Fin 4)) =
      Sparse.eval value969 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2551 (3 : Fin 4) = raw6270 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2551 raw6270; decide +kernel
    rw [heq]
    exact (canonical6270 hH).trans (sound969 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2551 + (injectiveMoment H (mergeFirst pivotMatrix2551 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2551 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2551, value1048, value969, value970, value974, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound52
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3373 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3373 = Sparse.eval value3373 (momentVector H) := by
  have heq : pivotMatrix3373 = (fun u v => node3373 (pivotPermutation3373 u) v) := by apply Matrix.ext; unfold pivotMatrix3373 node3373 pivotPermutation3373; decide +kernel
  have hmoment : injectiveMoment H node3373 = injectiveMoment H pivotMatrix3373 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix3373 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix3373 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix3373 (0 : Fin 5)) =
      Sparse.eval value2704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3373 (0 : Fin 5) = raw5676 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3373 raw5676; decide +kernel
    rw [heq]
    exact (canonical5676 hH).trans (sound2704 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix3373 (1 : Fin 5)) =
      Sparse.eval value2532 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3373 (1 : Fin 5) = raw6217 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3373 raw6217; decide +kernel
    rw [heq]
    exact (canonical6217 hH).trans (sound2532 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix3373 (2 : Fin 5)) =
      Sparse.eval value970 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3373 (2 : Fin 5) = raw6254 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3373 raw6254; decide +kernel
    rw [heq]
    exact (canonical6254 hH).trans (sound970 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix3373 (3 : Fin 5)) =
      Sparse.eval value2551 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3373 (3 : Fin 5) = raw6265 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3373 raw6265; decide +kernel
    rw [heq]
    exact (canonical6265 hH).trans (sound2551 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix3373 (4 : Fin 5)) =
      Sparse.eval value2531 (momentVector H) := by
    have heq : mergeFirst pivotMatrix3373 (4 : Fin 5) = raw6267 := by apply Matrix.ext; unfold mergeFirst pivotMatrix3373 raw6267; decide +kernel
    rw [heq]
    exact (canonical6267 hH).trans (sound2531 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node3373 + (injectiveMoment H (mergeFirst pivotMatrix3373 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3373 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3373 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3373 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix3373 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value3373, value2531, value2532, value2551, value2704, value970, Sparse.eval] at hc ⊢
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

theorem boundarySound83 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval boundaryRow83 (momentVector H) = 0 := by
  have hshape : boundaryMatrix83 0 = Pi.single (3 : Fin 4) 1 - Pi.single 0 1 := by
    funext j; fin_cases j <;> decide +kernel
  have hc := injectiveMoment_seven_row_boundary hH boundaryMatrix83 3 0 (by decide) hshape
  have hm0 : injectiveMoment H (mergeFirst boundaryMatrix83 (0 : Fin 6)) =
      Sparse.eval value2908 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (0 : Fin 6) = raw3368 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical3368 hH).trans (sound2908_e hH)
  have hm1 : injectiveMoment H (mergeFirst boundaryMatrix83 (1 : Fin 6)) =
      Sparse.eval value2910 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (1 : Fin 6) = raw7261 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7261 hH).trans (sound2910_e hH)
  have hm2 : injectiveMoment H (mergeFirst boundaryMatrix83 (2 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (2 : Fin 6) = raw7291 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7291 hH).trans (sound2914_e hH)
  have hm3 : injectiveMoment H (mergeFirst boundaryMatrix83 (3 : Fin 6)) =
      Sparse.eval value2910 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (3 : Fin 6) = raw7302 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7302 hH).trans (sound2910_e hH)
  have hm4 : injectiveMoment H (mergeFirst boundaryMatrix83 (4 : Fin 6)) =
      Sparse.eval value2914 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (4 : Fin 6) = raw7305 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7305 hH).trans (sound2914_e hH)
  have hm5 : injectiveMoment H (mergeFirst boundaryMatrix83 (5 : Fin 6)) =
      Sparse.eval value3373 (momentVector H) := by
    have heq : mergeFirst boundaryMatrix83 (5 : Fin 6) = raw7306 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7306 hH).trans (sound3373 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (injectiveMoment H (mergeFirst boundaryMatrix83 (0 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (1 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (2 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (3 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (4 : Fin 6)) + (injectiveMoment H (mergeFirst boundaryMatrix83 (5 : Fin 6)))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4, hm5] at hc
  norm_num [boundaryRow83, value2908, value2910, value2914, value3373, Sparse.eval, Integer.Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2243 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2243)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow83) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2243 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2243, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow83 (fun _ hH => PairSemantics.boundarySound83 hH)

theorem sourceRowsAt2240 : MixedData.sourceRows (2240 : Fin 2425) =
    MixedData.row2240 := by decide +kernel

theorem sourceRowsAt2241 : MixedData.sourceRows (2241 : Fin 2425) =
    MixedData.row2241 := by decide +kernel

theorem sourceRowsAt2242 : MixedData.sourceRows (2242 : Fin 2425) =
    MixedData.row2242 := by decide +kernel

theorem sourceRowsAt2243 : MixedData.sourceRows (2243 : Fin 2425) =
    MixedData.row2243 := by decide +kernel

theorem sourceRowsAt2244 : MixedData.sourceRows (2244 : Fin 2425) =
    MixedData.row2244 := by decide +kernel

theorem sourceRowsAt2245 : MixedData.sourceRows (2245 : Fin 2425) =
    MixedData.row2245 := by decide +kernel

theorem sourceRowsAt2246 : MixedData.sourceRows (2246 : Fin 2425) =
    MixedData.row2246 := by decide +kernel

theorem sourceRowsAt2247 : MixedData.sourceRows (2247 : Fin 2425) =
    MixedData.row2247 := by decide +kernel

theorem sourceRowsAt2248 : MixedData.sourceRows (2248 : Fin 2425) =
    MixedData.row2248 := by decide +kernel

theorem sourceRowsAt2249 : MixedData.sourceRows (2249 : Fin 2425) =
    MixedData.row2249 := by decide +kernel

theorem sourceRowsAt2250 : MixedData.sourceRows (2250 : Fin 2425) =
    MixedData.row2250 := by decide +kernel

theorem sourceRowsAt2251 : MixedData.sourceRows (2251 : Fin 2425) =
    MixedData.row2251 := by decide +kernel

theorem sourceRowsAt2252 : MixedData.sourceRows (2252 : Fin 2425) =
    MixedData.row2252 := by decide +kernel

theorem sourceRowsAt2253 : MixedData.sourceRows (2253 : Fin 2425) =
    MixedData.row2253 := by decide +kernel

theorem sourceRowsAt2254 : MixedData.sourceRows (2254 : Fin 2425) =
    MixedData.row2254 := by decide +kernel

theorem sourceRowsAt2255 : MixedData.sourceRows (2255 : Fin 2425) =
    MixedData.row2255 := by decide +kernel

theorem chunkSound140_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 140) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2240 ∨ k.val = 2241 ∨ k.val = 2242 ∨ k.val = 2243 ∨ k.val = 2244 ∨ k.val = 2245 ∨ k.val = 2246 ∨ k.val = 2247 ∨ k.val = 2248 ∨ k.val = 2249 ∨ k.val = 2250 ∨ k.val = 2251 ∨ k.val = 2252 ∨ k.val = 2253 ∨ k.val = 2254 ∨ k.val = 2255 := by omega
  rcases heq with h2240 | h2241 | h2242 | h2243 | h2244 | h2245 | h2246 | h2247 | h2248 | h2249 | h2250 | h2251 | h2252 | h2253 | h2254 | h2255
  · have he : k = (2240 : Fin 2425) := Fin.ext h2240
    subst k
    rw [sourceRowsAt2240]
    exact rowSound2240_e B hB hF
  · have he : k = (2241 : Fin 2425) := Fin.ext h2241
    subst k
    rw [sourceRowsAt2241]
    exact rowSound2241_e B hB hF
  · have he : k = (2242 : Fin 2425) := Fin.ext h2242
    subst k
    rw [sourceRowsAt2242]
    exact rowSound2242_e B hB hF
  · have he : k = (2243 : Fin 2425) := Fin.ext h2243
    subst k
    rw [sourceRowsAt2243]
    exact rowSound2243 B hB hF
  · have he : k = (2244 : Fin 2425) := Fin.ext h2244
    subst k
    rw [sourceRowsAt2244]
    exact rowSound2244_e B hB hF
  · have he : k = (2245 : Fin 2425) := Fin.ext h2245
    subst k
    rw [sourceRowsAt2245]
    exact rowSound2245_e B hB hF
  · have he : k = (2246 : Fin 2425) := Fin.ext h2246
    subst k
    rw [sourceRowsAt2246]
    exact rowSound2246_e B hB hF
  · have he : k = (2247 : Fin 2425) := Fin.ext h2247
    subst k
    rw [sourceRowsAt2247]
    exact rowSound2247_e B hB hF
  · have he : k = (2248 : Fin 2425) := Fin.ext h2248
    subst k
    rw [sourceRowsAt2248]
    exact rowSound2248_e B hB hF
  · have he : k = (2249 : Fin 2425) := Fin.ext h2249
    subst k
    rw [sourceRowsAt2249]
    exact rowSound2249_e B hB hF
  · have he : k = (2250 : Fin 2425) := Fin.ext h2250
    subst k
    rw [sourceRowsAt2250]
    exact rowSound2250_e B hB hF
  · have he : k = (2251 : Fin 2425) := Fin.ext h2251
    subst k
    rw [sourceRowsAt2251]
    exact rowSound2251_e B hB hF
  · have he : k = (2252 : Fin 2425) := Fin.ext h2252
    subst k
    rw [sourceRowsAt2252]
    exact rowSound2252_e B hB hF
  · have he : k = (2253 : Fin 2425) := Fin.ext h2253
    subst k
    rw [sourceRowsAt2253]
    exact rowSound2253_e B hB hF
  · have he : k = (2254 : Fin 2425) := Fin.ext h2254
    subst k
    rw [sourceRowsAt2254]
    exact rowSound2254_e B hB hF
  · have he : k = (2255 : Fin 2425) := Fin.ext h2255
    subst k
    rw [sourceRowsAt2255]
    exact rowSound2255_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e_oai
