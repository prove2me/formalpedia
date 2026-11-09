-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:51:41.796506+00:00
-- url     : https://prove2.me/submissions/c39eef73-4214-4a66-9e4c-53a5930674fc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2166_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2170_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2171_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2173_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2174_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2175_e

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

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

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

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
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

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical294
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37714 raw37714Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw37714 raw37714Labels = mixedMoment B raw37714step0 raw37714step0Labels := by
      have hz : ∀ j, raw37714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37714step0 = (fun i j => raw37714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37714step0 raw37714; decide +kernel
      have hl : raw37714step0Labels = raw37714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37714 raw37714Labels permutation346 hz
    mixedMoment B raw37714step0 raw37714step0Labels = mixedMoment B raw37714step1 raw37714step1Labels := by
      have ha : raw37714step1 = (fun i j => raw37714step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37714step1 raw37714step0; decide +kernel
      have hl : raw37714step1Labels = raw37714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37714step0 raw37714step0Labels permutation144 permutation2
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical37717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37717 raw37717Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw37717 raw37717Labels = mixedMoment B raw37717step0 raw37717step0Labels := by
      have hz : ∀ j, raw37717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37717step0 = (fun i j => raw37717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37717step0 raw37717; decide +kernel
      have hl : raw37717step0Labels = raw37717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37717 raw37717Labels permutation346 hz
    mixedMoment B raw37717step0 raw37717step0Labels = mixedMoment B raw37717step1 raw37717step1Labels := by
      have ha : raw37717step1 = (fun i j => raw37717step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37717step1 raw37717step0; decide +kernel
      have hl : raw37717step1Labels = raw37717step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37717step0 raw37717step0Labels permutation32 permutation4
    mixedMoment B raw37717step1 raw37717step1Labels = mixedMoment B raw37717step2 raw37717step2Labels := by
      have ha : raw37717step2 = -raw37717step1 := by apply Matrix.ext; change ∀ i j, raw37717step2 i j = -(raw37717step1 i j); unfold raw37717step2 raw37717step1; decide +kernel
      have hl : raw37717step2Labels = raw37717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2165 node2165Labels := by rfl

theorem canonical37720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37720 raw37720Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw37720 raw37720Labels = mixedMoment B raw37720step0 raw37720step0Labels := by
      have hz : ∀ j, raw37720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37720step0 = (fun i j => raw37720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37720step0 raw37720; decide +kernel
      have hl : raw37720step0Labels = raw37720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37720 raw37720Labels permutation346 hz
    mixedMoment B raw37720step0 raw37720step0Labels = mixedMoment B raw37720step1 raw37720step1Labels := by
      have ha : raw37720step1 = -raw37720step0 := by apply Matrix.ext; change ∀ i j, raw37720step1 i j = -(raw37720step0 i j); unfold raw37720step1 raw37720step0; decide +kernel
      have hl : raw37720step1Labels = raw37720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical37721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37721 raw37721Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw37721 raw37721Labels = mixedMoment B raw37721step0 raw37721step0Labels := by
      have hz : ∀ j, raw37721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37721step0 = (fun i j => raw37721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37721step0 raw37721; decide +kernel
      have hl : raw37721step0Labels = raw37721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37721 raw37721Labels permutation346 hz
    mixedMoment B raw37721step0 raw37721step0Labels = mixedMoment B raw37721step1 raw37721step1Labels := by
      have ha : raw37721step1 = (fun i j => raw37721step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37721step1 raw37721step0; decide +kernel
      have hl : raw37721step1Labels = raw37721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37721step0 raw37721step0Labels permutation144 permutation2
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical37733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37733 raw37733Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw37733 raw37733Labels = mixedMoment B raw37733step0 raw37733step0Labels := by
      have hz : ∀ j, raw37733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37733step0 = (fun i j => raw37733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37733step0 raw37733; decide +kernel
      have hl : raw37733step0Labels = raw37733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37733 raw37733Labels permutation346 hz
    mixedMoment B raw37733step0 raw37733step0Labels = mixedMoment B raw37733step1 raw37733step1Labels := by
      have ha : raw37733step1 = (fun i j => raw37733step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37733step1 raw37733step0; decide +kernel
      have hl : raw37733step1Labels = raw37733step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37733step0 raw37733step0Labels permutation32 permutation4
    mixedMoment B raw37733step1 raw37733step1Labels = mixedMoment B raw37733step2 raw37733step2Labels := by
      have ha : raw37733step2 = -raw37733step1 := by apply Matrix.ext; change ∀ i j, raw37733step2 i j = -(raw37733step1 i j); unfold raw37733step2 raw37733step1; decide +kernel
      have hl : raw37733step2Labels = raw37733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3420 node3420Labels := by rfl

theorem canonical37750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37750 raw37750Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw37750 raw37750Labels = mixedMoment B raw37750step0 raw37750step0Labels := by
      have ha : raw37750step0 = (fun i j => raw37750 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37750step0 raw37750; decide +kernel
      have hl : raw37750step0Labels = raw37750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37750 raw37750Labels permutation176 permutation4
    mixedMoment B raw37750step0 raw37750step0Labels = mixedMoment B raw37750step1 raw37750step1Labels := by
      have ha : raw37750step1 = -raw37750step0 := by apply Matrix.ext; change ∀ i j, raw37750step1 i j = -(raw37750step0 i j); unfold raw37750step1 raw37750step0; decide +kernel
      have hl : raw37750step1Labels = raw37750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical37751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37751 raw37751Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw37751 raw37751Labels = mixedMoment B raw37751step0 raw37751step0Labels := by
      have hz : ∀ j, raw37751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37751step0 = (fun i j => raw37751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37751step0 raw37751; decide +kernel
      have hl : raw37751step0Labels = raw37751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37751 raw37751Labels permutation346 hz
    mixedMoment B raw37751step0 raw37751step0Labels = mixedMoment B raw37751step1 raw37751step1Labels := by
      have ha : raw37751step1 = (fun i j => raw37751step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37751step1 raw37751step0; decide +kernel
      have hl : raw37751step1Labels = raw37751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37751step0 raw37751step0Labels permutation150 permutation2
    _ = mixedMoment B node3457 node3457Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical295
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37774 raw37774Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw37774 raw37774Labels = mixedMoment B raw37774step0 raw37774step0Labels := by
      have hz : ∀ j, raw37774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37774step0 = (fun i j => raw37774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37774step0 raw37774; decide +kernel
      have hl : raw37774step0Labels = raw37774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37774 raw37774Labels permutation346 hz
    mixedMoment B raw37774step0 raw37774step0Labels = mixedMoment B raw37774step1 raw37774step1Labels := by
      have ha : raw37774step1 = (fun i j => raw37774step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37774step1 raw37774step0; decide +kernel
      have hl : raw37774step1Labels = raw37774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37774step0 raw37774step0Labels permutation32 permutation4
    mixedMoment B raw37774step1 raw37774step1Labels = mixedMoment B raw37774step2 raw37774step2Labels := by
      have ha : raw37774step2 = -raw37774step1 := by apply Matrix.ext; change ∀ i j, raw37774step2 i j = -(raw37774step1 i j); unfold raw37774step2 raw37774step1; decide +kernel
      have hl : raw37774step2Labels = raw37774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3591 node3591Labels := by rfl

theorem canonical37775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37775 raw37775Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw37775 raw37775Labels = mixedMoment B raw37775step0 raw37775step0Labels := by
      have hz : ∀ j, raw37775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37775step0 = (fun i j => raw37775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37775step0 raw37775; decide +kernel
      have hl : raw37775step0Labels = raw37775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37775 raw37775Labels permutation346 hz
    mixedMoment B raw37775step0 raw37775step0Labels = mixedMoment B raw37775step1 raw37775step1Labels := by
      have ha : raw37775step1 = (fun i j => raw37775step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37775step1 raw37775step0; decide +kernel
      have hl : raw37775step1Labels = raw37775step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37775step0 raw37775step0Labels permutation40 permutation4
    mixedMoment B raw37775step1 raw37775step1Labels = mixedMoment B raw37775step2 raw37775step2Labels := by
      have ha : raw37775step2 = -raw37775step1 := by apply Matrix.ext; change ∀ i j, raw37775step2 i j = -(raw37775step1 i j); unfold raw37775step2 raw37775step1; decide +kernel
      have hl : raw37775step2Labels = raw37775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical37776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37776 raw37776Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw37776 raw37776Labels = mixedMoment B raw37776step0 raw37776step0Labels := by
      have ha : raw37776step0 = (fun i j => raw37776 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37776step0 raw37776; decide +kernel
      have hl : raw37776step0Labels = raw37776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37776 raw37776Labels permutation160 permutation4
    mixedMoment B raw37776step0 raw37776step0Labels = mixedMoment B raw37776step1 raw37776step1Labels := by
      have ha : raw37776step1 = -raw37776step0 := by apply Matrix.ext; change ∀ i j, raw37776step1 i j = -(raw37776step0 i j); unfold raw37776step1 raw37776step0; decide +kernel
      have hl : raw37776step1Labels = raw37776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical37777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37777 raw37777Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw37777 raw37777Labels = mixedMoment B raw37777step0 raw37777step0Labels := by
      have hz : ∀ j, raw37777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37777step0 = (fun i j => raw37777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37777step0 raw37777; decide +kernel
      have hl : raw37777step0Labels = raw37777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37777 raw37777Labels permutation346 hz
    mixedMoment B raw37777step0 raw37777step0Labels = mixedMoment B raw37777step1 raw37777step1Labels := by
      have ha : raw37777step1 = (fun i j => raw37777step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37777step1 raw37777step0; decide +kernel
      have hl : raw37777step1Labels = raw37777step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37777step0 raw37777step0Labels permutation34 permutation4
    mixedMoment B raw37777step1 raw37777step1Labels = mixedMoment B raw37777step2 raw37777step2Labels := by
      have ha : raw37777step2 = -raw37777step1 := by apply Matrix.ext; change ∀ i j, raw37777step2 i j = -(raw37777step1 i j); unfold raw37777step2 raw37777step1; decide +kernel
      have hl : raw37777step2Labels = raw37777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2157 node2157Labels := by rfl

theorem canonical37778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37778 raw37778Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw37778 raw37778Labels = mixedMoment B raw37778step0 raw37778step0Labels := by
      have hz : ∀ j, raw37778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37778step0 = (fun i j => raw37778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37778step0 raw37778; decide +kernel
      have hl : raw37778step0Labels = raw37778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37778 raw37778Labels permutation346 hz
    mixedMoment B raw37778step0 raw37778step0Labels = mixedMoment B raw37778step1 raw37778step1Labels := by
      have ha : raw37778step1 = (fun i j => raw37778step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37778step1 raw37778step0; decide +kernel
      have hl : raw37778step1Labels = raw37778step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37778step0 raw37778step0Labels permutation32 permutation4
    mixedMoment B raw37778step1 raw37778step1Labels = mixedMoment B raw37778step2 raw37778step2Labels := by
      have ha : raw37778step2 = -raw37778step1 := by apply Matrix.ext; change ∀ i j, raw37778step2 i j = -(raw37778step1 i j); unfold raw37778step2 raw37778step1; decide +kernel
      have hl : raw37778step2Labels = raw37778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical37779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37779 raw37779Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw37779 raw37779Labels = mixedMoment B raw37779step0 raw37779step0Labels := by
      have hz : ∀ j, raw37779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37779step0 = (fun i j => raw37779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37779step0 raw37779; decide +kernel
      have hl : raw37779step0Labels = raw37779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37779 raw37779Labels permutation346 hz
    mixedMoment B raw37779step0 raw37779step0Labels = mixedMoment B raw37779step1 raw37779step1Labels := by
      have ha : raw37779step1 = (fun i j => raw37779step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37779step1 raw37779step0; decide +kernel
      have hl : raw37779step1Labels = raw37779step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37779step0 raw37779step0Labels permutation32 permutation4
    mixedMoment B raw37779step1 raw37779step1Labels = mixedMoment B raw37779step2 raw37779step2Labels := by
      have ha : raw37779step2 = -raw37779step1 := by apply Matrix.ext; change ∀ i j, raw37779step2 i j = -(raw37779step1 i j); unfold raw37779step2 raw37779step1; decide +kernel
      have hl : raw37779step2Labels = raw37779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical37780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37780 raw37780Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw37780 raw37780Labels = mixedMoment B raw37780step0 raw37780step0Labels := by
      have hz : ∀ j, raw37780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37780step0 = (fun i j => raw37780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37780step0 raw37780; decide +kernel
      have hl : raw37780step0Labels = raw37780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37780 raw37780Labels permutation346 hz
    mixedMoment B raw37780step0 raw37780step0Labels = mixedMoment B raw37780step1 raw37780step1Labels := by
      have ha : raw37780step1 = -raw37780step0 := by apply Matrix.ext; change ∀ i j, raw37780step1 i j = -(raw37780step0 i j); unfold raw37780step1 raw37780step0; decide +kernel
      have hl : raw37780step1Labels = raw37780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

theorem canonical37781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37781 raw37781Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw37781 raw37781Labels = mixedMoment B raw37781step0 raw37781step0Labels := by
      have hz : ∀ j, raw37781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37781step0 = (fun i j => raw37781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37781step0 raw37781; decide +kernel
      have hl : raw37781step0Labels = raw37781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37781 raw37781Labels permutation346 hz
    mixedMoment B raw37781step0 raw37781step0Labels = mixedMoment B raw37781step1 raw37781step1Labels := by
      have ha : raw37781step1 = (fun i j => raw37781step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37781step1 raw37781step0; decide +kernel
      have hl : raw37781step1Labels = raw37781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37781step0 raw37781step0Labels permutation34 permutation4
    mixedMoment B raw37781step1 raw37781step1Labels = mixedMoment B raw37781step2 raw37781step2Labels := by
      have ha : raw37781step2 = -raw37781step1 := by apply Matrix.ext; change ∀ i j, raw37781step2 i j = -(raw37781step1 i j); unfold raw37781step2 raw37781step1; decide +kernel
      have hl : raw37781step2Labels = raw37781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical37782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37782 raw37782Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw37782 raw37782Labels = mixedMoment B raw37782step0 raw37782step0Labels := by
      have hz : ∀ j, raw37782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37782step0 = (fun i j => raw37782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37782step0 raw37782; decide +kernel
      have hl : raw37782step0Labels = raw37782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37782 raw37782Labels permutation346 hz
    mixedMoment B raw37782step0 raw37782step0Labels = mixedMoment B raw37782step1 raw37782step1Labels := by
      have ha : raw37782step1 = (fun i j => raw37782step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37782step1 raw37782step0; decide +kernel
      have hl : raw37782step1Labels = raw37782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37782step0 raw37782step0Labels permutation44 permutation4
    mixedMoment B raw37782step1 raw37782step1Labels = mixedMoment B raw37782step2 raw37782step2Labels := by
      have ha : raw37782step2 = -raw37782step1 := by apply Matrix.ext; change ∀ i j, raw37782step2 i j = -(raw37782step1 i j); unfold raw37782step2 raw37782step1; decide +kernel
      have hl : raw37782step2Labels = raw37782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical37783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37783 raw37783Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw37783 raw37783Labels = mixedMoment B raw37783step0 raw37783step0Labels := by
      have ha : raw37783step0 = (fun i j => raw37783 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37783step0 raw37783; decide +kernel
      have hl : raw37783step0Labels = raw37783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37783 raw37783Labels permutation164 permutation4
    mixedMoment B raw37783step0 raw37783step0Labels = mixedMoment B raw37783step1 raw37783step1Labels := by
      have ha : raw37783step1 = -raw37783step0 := by apply Matrix.ext; change ∀ i j, raw37783step1 i j = -(raw37783step0 i j); unfold raw37783step1 raw37783step0; decide +kernel
      have hl : raw37783step1Labels = raw37783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical37784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37784 raw37784Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw37784 raw37784Labels = mixedMoment B raw37784step0 raw37784step0Labels := by
      have hz : ∀ j, raw37784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37784step0 = (fun i j => raw37784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37784step0 raw37784; decide +kernel
      have hl : raw37784step0Labels = raw37784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37784 raw37784Labels permutation346 hz
    mixedMoment B raw37784step0 raw37784step0Labels = mixedMoment B raw37784step1 raw37784step1Labels := by
      have ha : raw37784step1 = (fun i j => raw37784step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37784step1 raw37784step0; decide +kernel
      have hl : raw37784step1Labels = raw37784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37784step0 raw37784step0Labels permutation35 permutation4
    mixedMoment B raw37784step1 raw37784step1Labels = mixedMoment B raw37784step2 raw37784step2Labels := by
      have ha : raw37784step2 = -raw37784step1 := by apply Matrix.ext; change ∀ i j, raw37784step2 i j = -(raw37784step1 i j); unfold raw37784step2 raw37784step1; decide +kernel
      have hl : raw37784step2Labels = raw37784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical37785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37785 raw37785Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw37785 raw37785Labels = mixedMoment B raw37785step0 raw37785step0Labels := by
      have hz : ∀ j, raw37785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37785step0 = (fun i j => raw37785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37785step0 raw37785; decide +kernel
      have hl : raw37785step0Labels = raw37785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37785 raw37785Labels permutation346 hz
    mixedMoment B raw37785step0 raw37785step0Labels = mixedMoment B raw37785step1 raw37785step1Labels := by
      have ha : raw37785step1 = (fun i j => raw37785step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37785step1 raw37785step0; decide +kernel
      have hl : raw37785step1Labels = raw37785step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37785step0 raw37785step0Labels permutation32 permutation4
    mixedMoment B raw37785step1 raw37785step1Labels = mixedMoment B raw37785step2 raw37785step2Labels := by
      have ha : raw37785step2 = -raw37785step1 := by apply Matrix.ext; change ∀ i j, raw37785step2 i j = -(raw37785step1 i j); unfold raw37785step2 raw37785step1; decide +kernel
      have hl : raw37785step2Labels = raw37785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2166 node2166Labels := by rfl

theorem canonical37786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37786 raw37786Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw37786 raw37786Labels = mixedMoment B raw37786step0 raw37786step0Labels := by
      have hz : ∀ j, raw37786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37786step0 = (fun i j => raw37786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37786step0 raw37786; decide +kernel
      have hl : raw37786step0Labels = raw37786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37786 raw37786Labels permutation346 hz
    mixedMoment B raw37786step0 raw37786step0Labels = mixedMoment B raw37786step1 raw37786step1Labels := by
      have ha : raw37786step1 = (fun i j => raw37786step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37786step1 raw37786step0; decide +kernel
      have hl : raw37786step1Labels = raw37786step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37786step0 raw37786step0Labels permutation32 permutation4
    mixedMoment B raw37786step1 raw37786step1Labels = mixedMoment B raw37786step2 raw37786step2Labels := by
      have ha : raw37786step2 = -raw37786step1 := by apply Matrix.ext; change ∀ i j, raw37786step2 i j = -(raw37786step1 i j); unfold raw37786step2 raw37786step1; decide +kernel
      have hl : raw37786step2Labels = raw37786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3592 node3592Labels := by rfl

theorem canonical37787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37787 raw37787Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw37787 raw37787Labels = mixedMoment B raw37787step0 raw37787step0Labels := by
      have hz : ∀ j, raw37787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37787step0 = (fun i j => raw37787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37787step0 raw37787; decide +kernel
      have hl : raw37787step0Labels = raw37787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37787 raw37787Labels permutation346 hz
    mixedMoment B raw37787step0 raw37787step0Labels = mixedMoment B raw37787step1 raw37787step1Labels := by
      have ha : raw37787step1 = (fun i j => raw37787step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37787step1 raw37787step0; decide +kernel
      have hl : raw37787step1Labels = raw37787step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37787step0 raw37787step0Labels permutation38 permutation4
    mixedMoment B raw37787step1 raw37787step1Labels = mixedMoment B raw37787step2 raw37787step2Labels := by
      have ha : raw37787step2 = -raw37787step1 := by apply Matrix.ext; change ∀ i j, raw37787step2 i j = -(raw37787step1 i j); unfold raw37787step2 raw37787step1; decide +kernel
      have hl : raw37787step2Labels = raw37787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical37788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37788 raw37788Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw37788 raw37788Labels = mixedMoment B raw37788step0 raw37788step0Labels := by
      have ha : raw37788step0 = (fun i j => raw37788 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37788step0 raw37788; decide +kernel
      have hl : raw37788step0Labels = raw37788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37788 raw37788Labels permutation158 permutation4
    mixedMoment B raw37788step0 raw37788step0Labels = mixedMoment B raw37788step1 raw37788step1Labels := by
      have ha : raw37788step1 = -raw37788step0 := by apply Matrix.ext; change ∀ i j, raw37788step1 i j = -(raw37788step0 i j); unfold raw37788step1 raw37788step0; decide +kernel
      have hl : raw37788step1Labels = raw37788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical37789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37789 raw37789Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw37789 raw37789Labels = mixedMoment B raw37789step0 raw37789step0Labels := by
      have hz : ∀ j, raw37789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37789step0 = (fun i j => raw37789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37789step0 raw37789; decide +kernel
      have hl : raw37789step0Labels = raw37789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37789 raw37789Labels permutation346 hz
    mixedMoment B raw37789step0 raw37789step0Labels = mixedMoment B raw37789step1 raw37789step1Labels := by
      have ha : raw37789step1 = (fun i j => raw37789step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37789step1 raw37789step0; decide +kernel
      have hl : raw37789step1Labels = raw37789step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37789step0 raw37789step0Labels permutation33 permutation4
    mixedMoment B raw37789step1 raw37789step1Labels = mixedMoment B raw37789step2 raw37789step2Labels := by
      have ha : raw37789step2 = -raw37789step1 := by apply Matrix.ext; change ∀ i j, raw37789step2 i j = -(raw37789step1 i j); unfold raw37789step2 raw37789step1; decide +kernel
      have hl : raw37789step2Labels = raw37789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical37790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37790 raw37790Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw37790 raw37790Labels = mixedMoment B raw37790step0 raw37790step0Labels := by
      have hz : ∀ j, raw37790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37790step0 = (fun i j => raw37790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37790step0 raw37790; decide +kernel
      have hl : raw37790step0Labels = raw37790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37790 raw37790Labels permutation346 hz
    mixedMoment B raw37790step0 raw37790step0Labels = mixedMoment B raw37790step1 raw37790step1Labels := by
      have ha : raw37790step1 = (fun i j => raw37790step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37790step1 raw37790step0; decide +kernel
      have hl : raw37790step1Labels = raw37790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37790step0 raw37790step0Labels permutation36 permutation2
    mixedMoment B raw37790step1 raw37790step1Labels = mixedMoment B raw37790step2 raw37790step2Labels := by
      have ha : raw37790step2 = -raw37790step1 := by apply Matrix.ext; change ∀ i j, raw37790step2 i j = -(raw37790step1 i j); unfold raw37790step2 raw37790step1; decide +kernel
      have hl : raw37790step2Labels = raw37790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical37791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37791 raw37791Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw37791 raw37791Labels = mixedMoment B raw37791step0 raw37791step0Labels := by
      have ha : raw37791step0 = (fun i j => raw37791 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37791step0 raw37791; decide +kernel
      have hl : raw37791step0Labels = raw37791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37791 raw37791Labels permutation160 permutation4
    mixedMoment B raw37791step0 raw37791step0Labels = mixedMoment B raw37791step1 raw37791step1Labels := by
      have ha : raw37791step1 = -raw37791step0 := by apply Matrix.ext; change ∀ i j, raw37791step1 i j = -(raw37791step0 i j); unfold raw37791step1 raw37791step0; decide +kernel
      have hl : raw37791step1Labels = raw37791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical37792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37792 raw37792Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw37792 raw37792Labels = mixedMoment B raw37792step0 raw37792step0Labels := by
      have hz : ∀ j, raw37792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37792step0 = (fun i j => raw37792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37792step0 raw37792; decide +kernel
      have hl : raw37792step0Labels = raw37792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37792 raw37792Labels permutation346 hz
    mixedMoment B raw37792step0 raw37792step0Labels = mixedMoment B raw37792step1 raw37792step1Labels := by
      have ha : raw37792step1 = (fun i j => raw37792step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37792step1 raw37792step0; decide +kernel
      have hl : raw37792step1Labels = raw37792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37792step0 raw37792step0Labels permutation34 permutation4
    mixedMoment B raw37792step1 raw37792step1Labels = mixedMoment B raw37792step2 raw37792step2Labels := by
      have ha : raw37792step2 = -raw37792step1 := by apply Matrix.ext; change ∀ i j, raw37792step2 i j = -(raw37792step1 i j); unfold raw37792step2 raw37792step1; decide +kernel
      have hl : raw37792step2Labels = raw37792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical37793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37793 raw37793Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw37793 raw37793Labels = mixedMoment B raw37793step0 raw37793step0Labels := by
      have hz : ∀ j, raw37793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37793step0 = (fun i j => raw37793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37793step0 raw37793; decide +kernel
      have hl : raw37793step0Labels = raw37793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37793 raw37793Labels permutation346 hz
    mixedMoment B raw37793step0 raw37793step0Labels = mixedMoment B raw37793step1 raw37793step1Labels := by
      have ha : raw37793step1 = (fun i j => raw37793step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37793step1 raw37793step0; decide +kernel
      have hl : raw37793step1Labels = raw37793step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37793step0 raw37793step0Labels permutation32 permutation4
    mixedMoment B raw37793step1 raw37793step1Labels = mixedMoment B raw37793step2 raw37793step2Labels := by
      have ha : raw37793step2 = -raw37793step1 := by apply Matrix.ext; change ∀ i j, raw37793step2 i j = -(raw37793step1 i j); unfold raw37793step2 raw37793step1; decide +kernel
      have hl : raw37793step2Labels = raw37793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3412 node3412Labels := by rfl

theorem canonical37794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37794 raw37794Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw37794 raw37794Labels = mixedMoment B raw37794step0 raw37794step0Labels := by
      have hz : ∀ j, raw37794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37794step0 = (fun i j => raw37794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37794step0 raw37794; decide +kernel
      have hl : raw37794step0Labels = raw37794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37794 raw37794Labels permutation346 hz
    mixedMoment B raw37794step0 raw37794step0Labels = mixedMoment B raw37794step1 raw37794step1Labels := by
      have ha : raw37794step1 = (fun i j => raw37794step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37794step1 raw37794step0; decide +kernel
      have hl : raw37794step1Labels = raw37794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37794step0 raw37794step0Labels permutation151 permutation4
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical37819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37819 raw37819Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw37819 raw37819Labels = mixedMoment B raw37819step0 raw37819step0Labels := by
      have ha : raw37819step0 = (fun i j => raw37819 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37819step0 raw37819; decide +kernel
      have hl : raw37819step0Labels = raw37819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37819 raw37819Labels permutation152 permutation4
    mixedMoment B raw37819step0 raw37819step0Labels = mixedMoment B raw37819step1 raw37819step1Labels := by
      have ha : raw37819step1 = -raw37819step0 := by apply Matrix.ext; change ∀ i j, raw37819step1 i j = -(raw37819step0 i j); unfold raw37819step1 raw37819step0; decide +kernel
      have hl : raw37819step1Labels = raw37819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2182 node2182Labels := by rfl

theorem canonical37820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37820 raw37820Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37820 raw37820Labels = mixedMoment B raw37820step0 raw37820step0Labels := by
      have ha : raw37820step0 = (fun i j => raw37820 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37820step0 raw37820; decide +kernel
      have hl : raw37820step0Labels = raw37820Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37820 raw37820Labels permutation152 permutation4
    mixedMoment B raw37820step0 raw37820step0Labels = mixedMoment B raw37820step1 raw37820step1Labels := by
      have ha : raw37820step1 = -raw37820step0 := by apply Matrix.ext; change ∀ i j, raw37820step1 i j = -(raw37820step0 i j); unfold raw37820step1 raw37820step0; decide +kernel
      have hl : raw37820step1Labels = raw37820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical37821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37821 raw37821Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37821 raw37821Labels = mixedMoment B raw37821step0 raw37821step0Labels := by
      have ha : raw37821step0 = (fun i j => raw37821 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37821step0 raw37821; decide +kernel
      have hl : raw37821step0Labels = raw37821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37821 raw37821Labels permutation176 permutation4
    mixedMoment B raw37821step0 raw37821step0Labels = mixedMoment B raw37821step1 raw37821step1Labels := by
      have ha : raw37821step1 = -raw37821step0 := by apply Matrix.ext; change ∀ i j, raw37821step1 i j = -(raw37821step0 i j); unfold raw37821step1 raw37821step0; decide +kernel
      have hl : raw37821step1Labels = raw37821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical37822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37822 raw37822Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37822 raw37822Labels = mixedMoment B raw37822step0 raw37822step0Labels := by
      have ha : raw37822step0 = (fun i j => raw37822 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37822step0 raw37822; decide +kernel
      have hl : raw37822step0Labels = raw37822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37822 raw37822Labels permutation662 permutation2
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical37823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37823 raw37823Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37823 raw37823Labels = mixedMoment B raw37823step0 raw37823step0Labels := by
      have ha : raw37823step0 = (fun i j => raw37823 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37823step0 raw37823; decide +kernel
      have hl : raw37823step0Labels = raw37823Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37823 raw37823Labels permutation686 permutation2
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical37824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37824 raw37824Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw37824 raw37824Labels = mixedMoment B raw37824step0 raw37824step0Labels := by
      have ha : raw37824step0 = (fun i j => raw37824 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37824step0 raw37824; decide +kernel
      have hl : raw37824step0Labels = raw37824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37824 raw37824Labels permutation662 permutation2
    _ = mixedMoment B node2182 node2182Labels := by rfl

theorem canonical37825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37825 raw37825Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw37825 raw37825Labels = mixedMoment B raw37825step0 raw37825step0Labels := by
      have ha : raw37825step0 = (fun i j => raw37825 (permutation662 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37825step0 raw37825; decide +kernel
      have hl : raw37825step0Labels = raw37825Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37825 raw37825Labels permutation662 permutation0
    _ = mixedMoment B node4077 node4077Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2144 node2144Labels = Sparse.eval nodeValue2144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2144) = mixedMoment B node2144 node2144Labels := rfl
  simpa [nodeValue2144, Sparse.eval] using hc.symm

theorem sound2146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2146 node2146Labels = Sparse.eval nodeValue2146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2146) = mixedMoment B node2146 node2146Labels := rfl
  simpa [nodeValue2146, Sparse.eval] using hc.symm

theorem sound2148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2148 node2148Labels = Sparse.eval nodeValue2148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2148) = mixedMoment B node2148 node2148Labels := rfl
  simpa [nodeValue2148, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2154 node2154Labels = Sparse.eval nodeValue2154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2154) = mixedMoment B node2154 node2154Labels := rfl
  simpa [nodeValue2154, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

theorem sound2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2166 node2166Labels = Sparse.eval nodeValue2166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2166) = mixedMoment B node2166 node2166Labels := rfl
  simpa [nodeValue2166, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2182 node2182Labels = Sparse.eval nodeValue2182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2182) = mixedMoment B node2182 node2182Labels := rfl
  simpa [nodeValue2182, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2249 node2249Labels = Sparse.eval nodeValue2249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2249) = mixedMoment B node2249 node2249Labels := rfl
  simpa [nodeValue2249, Sparse.eval] using hc.symm

theorem sound2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2257 node2257Labels = Sparse.eval nodeValue2257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2257) = mixedMoment B node2257 node2257Labels := rfl
  simpa [nodeValue2257, Sparse.eval] using hc.symm

theorem sound2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2272 node2272Labels = Sparse.eval nodeValue2272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2272) = mixedMoment B node2272 node2272Labels := rfl
  simpa [nodeValue2272, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

theorem sound3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3455 node3455Labels = Sparse.eval nodeValue3455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3455) = mixedMoment B node3455 node3455Labels := rfl
  simpa [nodeValue3455, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

theorem sound3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3592 node3592Labels = Sparse.eval nodeValue3592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3592) = mixedMoment B node3592 node3592Labels := rfl
  simpa [nodeValue3592, Sparse.eval] using hc.symm

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4074 node4074Labels = Sparse.eval nodeValue4074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4074) = mixedMoment B node4074 node4074Labels := rfl
  simpa [nodeValue4074, Sparse.eval] using hc.symm

theorem sound4075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4075 node4075Labels = Sparse.eval nodeValue4075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4075) = mixedMoment B node4075 node4075Labels := rfl
  simpa [nodeValue4075, Sparse.eval] using hc.symm

theorem sound4077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4077 node4077Labels = Sparse.eval nodeValue4077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4077) = mixedMoment B node4077 node4077Labels := rfl
  simpa [nodeValue4077, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources85
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2748 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 0) (sourceB2748 + difference 0 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 0) (sourceB2748 + difference 0 2) sourceC2748) = raw37717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37717; decide +kernel
    rw [ha]
    exact (canonical37717 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 1) (sourceB2748 + difference 1 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 1) (sourceB2748 + difference 1 2) sourceC2748) = raw37733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37733; decide +kernel
    rw [ha]
    exact (canonical37733 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 2) (sourceB2748 + difference 2 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 2) (sourceB2748 + difference 2 2) sourceC2748) = raw37750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37750; decide +kernel
    rw [ha]
    exact (canonical37750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 3) (sourceB2748 + difference 3 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 3) (sourceB2748 + difference 3 2) sourceC2748) = raw37714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37714; decide +kernel
    rw [ha]
    exact (canonical37714 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 4) (sourceB2748 + difference 4 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 4) (sourceB2748 + difference 4 2) sourceC2748) = raw37751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37751; decide +kernel
    rw [ha]
    exact (canonical37751 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2748 + difference 2 5) (sourceB2748 + difference 5 2) sourceC2748) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2748 + difference 2 5) (sourceB2748 + difference 5 2) sourceC2748) = raw37721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2748 sourceB2748 sourceC2748 difference raw37721; decide +kernel
    rw [ha]
    exact (canonical37721 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2748 + sourceB2748) sourceC2748) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (doubleCharges (sourceA2748 + sourceB2748) sourceC2748) = raw37720 := by
      apply Matrix.ext; unfold doubleCharges sourceA2748 sourceB2748 sourceC2748 raw37720; decide +kernel
    rw [ha]
    exact (canonical37720 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2748 sourceB2748 sourceC2748
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2748, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources86
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2756 + difference 0 5) (sourceB2756 + difference 5 0) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2756 + difference 0 5) (sourceB2756 + difference 5 0) sourceC2756) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2756 + difference 1 5) (sourceB2756 + difference 5 1) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2756 + difference 1 5) (sourceB2756 + difference 5 1) sourceC2756) = raw37775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37775; decide +kernel
    rw [ha]
    exact (canonical37775 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2756 + difference 2 5) (sourceB2756 + difference 5 2) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2756 + difference 2 5) (sourceB2756 + difference 5 2) sourceC2756) = raw37776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37776; decide +kernel
    rw [ha]
    exact (canonical37776 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2756 + difference 3 5) (sourceB2756 + difference 5 3) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2756 + difference 3 5) (sourceB2756 + difference 5 3) sourceC2756) = raw37777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37777; decide +kernel
    rw [ha]
    exact (canonical37777 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2756 + difference 4 5) (sourceB2756 + difference 5 4) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2756 + difference 4 5) (sourceB2756 + difference 5 4) sourceC2756) = raw37778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37778; decide +kernel
    rw [ha]
    exact (canonical37778 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2756 + difference 5 5) (sourceB2756 + difference 5 5) sourceC2756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2756 + difference 5 5) (sourceB2756 + difference 5 5) sourceC2756) = raw37779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2756 sourceB2756 sourceC2756 difference raw37779; decide +kernel
    rw [ha]
    exact (canonical37779 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2756 + sourceB2756) sourceC2756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2756 + sourceB2756) sourceC2756) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2756 sourceB2756 sourceC2756 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2756 sourceB2756 sourceC2756
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2756, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2757 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2757 + difference 0 3) (sourceB2757 + difference 3 0) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2757 + difference 0 3) (sourceB2757 + difference 3 0) sourceC2757) = raw37781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37781; decide +kernel
    rw [ha]
    exact (canonical37781 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2757 + difference 1 3) (sourceB2757 + difference 3 1) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2757 + difference 1 3) (sourceB2757 + difference 3 1) sourceC2757) = raw37782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37782; decide +kernel
    rw [ha]
    exact (canonical37782 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2757 + difference 2 3) (sourceB2757 + difference 3 2) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2757 + difference 2 3) (sourceB2757 + difference 3 2) sourceC2757) = raw37783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37783; decide +kernel
    rw [ha]
    exact (canonical37783 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2757 + difference 3 3) (sourceB2757 + difference 3 3) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2757 + difference 3 3) (sourceB2757 + difference 3 3) sourceC2757) = raw37784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37784; decide +kernel
    rw [ha]
    exact (canonical37784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2757 + difference 4 3) (sourceB2757 + difference 3 4) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2757 + difference 4 3) (sourceB2757 + difference 3 4) sourceC2757) = raw37785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37785; decide +kernel
    rw [ha]
    exact (canonical37785 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2757 + difference 5 3) (sourceB2757 + difference 3 5) sourceC2757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2757 + difference 5 3) (sourceB2757 + difference 3 5) sourceC2757) = raw37777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2757 sourceB2757 sourceC2757 difference raw37777; decide +kernel
    rw [ha]
    exact (canonical37777 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2757 + sourceB2757) sourceC2757) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2757 + sourceB2757) sourceC2757) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2757 sourceB2757 sourceC2757 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2757 sourceB2757 sourceC2757
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2757, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2758 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2758 + difference 0 2) (sourceB2758 + difference 2 0) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2758 + difference 0 2) (sourceB2758 + difference 2 0) sourceC2758) = raw37786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37786; decide +kernel
    rw [ha]
    exact (canonical37786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2758 + difference 1 2) (sourceB2758 + difference 2 1) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2758 + difference 1 2) (sourceB2758 + difference 2 1) sourceC2758) = raw37787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37787; decide +kernel
    rw [ha]
    exact (canonical37787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2758 + difference 2 2) (sourceB2758 + difference 2 2) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2758 + difference 2 2) (sourceB2758 + difference 2 2) sourceC2758) = raw37788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37788; decide +kernel
    rw [ha]
    exact (canonical37788 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2758 + difference 3 2) (sourceB2758 + difference 2 3) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2758 + difference 3 2) (sourceB2758 + difference 2 3) sourceC2758) = raw37785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37785; decide +kernel
    rw [ha]
    exact (canonical37785 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2758 + difference 4 2) (sourceB2758 + difference 2 4) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2758 + difference 4 2) (sourceB2758 + difference 2 4) sourceC2758) = raw37789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37789; decide +kernel
    rw [ha]
    exact (canonical37789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2758 + difference 5 2) (sourceB2758 + difference 2 5) sourceC2758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2758 + difference 5 2) (sourceB2758 + difference 2 5) sourceC2758) = raw37778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2758 sourceB2758 sourceC2758 difference raw37778; decide +kernel
    rw [ha]
    exact (canonical37778 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2758 + sourceB2758) sourceC2758) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2758 + sourceB2758) sourceC2758) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2758 sourceB2758 sourceC2758 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2758 sourceB2758 sourceC2758
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2758, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2759 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2759 + difference 0 5) (sourceB2759 + difference 5 0) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2759 + difference 0 5) (sourceB2759 + difference 5 0) sourceC2759) = raw37790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37790; decide +kernel
    rw [ha]
    exact (canonical37790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2759 + difference 1 5) (sourceB2759 + difference 5 1) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2759 + difference 1 5) (sourceB2759 + difference 5 1) sourceC2759) = raw37774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37774; decide +kernel
    rw [ha]
    exact (canonical37774 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2759 + difference 2 5) (sourceB2759 + difference 5 2) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2759 + difference 2 5) (sourceB2759 + difference 5 2) sourceC2759) = raw37791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37791; decide +kernel
    rw [ha]
    exact (canonical37791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2759 + difference 3 5) (sourceB2759 + difference 5 3) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2759 + difference 3 5) (sourceB2759 + difference 5 3) sourceC2759) = raw37792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37792; decide +kernel
    rw [ha]
    exact (canonical37792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2759 + difference 4 5) (sourceB2759 + difference 5 4) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2759 + difference 4 5) (sourceB2759 + difference 5 4) sourceC2759) = raw37793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37793; decide +kernel
    rw [ha]
    exact (canonical37793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2759 + difference 5 5) (sourceB2759 + difference 5 5) sourceC2759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2759 + difference 5 5) (sourceB2759 + difference 5 5) sourceC2759) = raw37794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2759 sourceB2759 sourceC2759 difference raw37794; decide +kernel
    rw [ha]
    exact (canonical37794 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2759 + sourceB2759) sourceC2759) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (doubleCharges (sourceA2759 + sourceB2759) sourceC2759) = raw37780 := by
      apply Matrix.ext; unfold doubleCharges sourceA2759 sourceB2759 sourceC2759 raw37780; decide +kernel
    rw [ha]
    exact (canonical37780 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2759 sourceB2759 sourceC2759
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2759, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2766 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 0) (sourceB2766 + difference 0 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 0) (sourceB2766 + difference 0 3) sourceC2766) = raw37819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37819; decide +kernel
    rw [ha]
    exact (canonical37819 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 1) (sourceB2766 + difference 1 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 1) (sourceB2766 + difference 1 3) sourceC2766) = raw37820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37820; decide +kernel
    rw [ha]
    exact (canonical37820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 2) (sourceB2766 + difference 2 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 2) (sourceB2766 + difference 2 3) sourceC2766) = raw37821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37821; decide +kernel
    rw [ha]
    exact (canonical37821 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 3) (sourceB2766 + difference 3 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 3) (sourceB2766 + difference 3 3) sourceC2766) = raw37822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37822; decide +kernel
    rw [ha]
    exact (canonical37822 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 4) (sourceB2766 + difference 4 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 4) (sourceB2766 + difference 4 3) sourceC2766) = raw37823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37823; decide +kernel
    rw [ha]
    exact (canonical37823 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2766 + difference 3 5) (sourceB2766 + difference 5 3) sourceC2766) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA2766 + difference 3 5) (sourceB2766 + difference 5 3) sourceC2766) = raw37824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2766 sourceB2766 sourceC2766 difference raw37824; decide +kernel
    rw [ha]
    exact (canonical37824 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2766 + sourceB2766) sourceC2766) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (doubleCharges (sourceA2766 + sourceB2766) sourceC2766) = raw37825 := by
      apply Matrix.ext; unfold doubleCharges sourceA2766 sourceB2766 sourceC2766 raw37825; decide +kernel
    rw [ha]
    exact (canonical37825 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2766 sourceB2766 sourceC2766
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2766, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2160 : Integer.Sparse.reindex keyMap MixedData.row2160 = numericRow2160 := by decide +kernel

theorem numericCheck2160 (x : Master → ℝ) : Integer.Sparse.eval numericRow2160 x =
    (1 : ℝ) * reducedSource2160 x := by
  norm_num [numericRow2160, reducedSource2160, Integer.Sparse.eval, Sparse.eval, nodeValue2165, nodeValue2186, nodeValue3420, nodeValue3457, nodeValue3510, nodeValue4074]

theorem reindexCheck2161 : Integer.Sparse.reindex keyMap MixedData.row2161 = numericRow2161 := by decide +kernel

theorem numericCheck2161 (x : Master → ℝ) : Integer.Sparse.eval numericRow2161 x =
    (1 : ℝ) * reducedSource2161 x := by
  norm_num [numericRow2161, reducedSource2161, Integer.Sparse.eval, Sparse.eval, nodeValue2144, nodeValue2146, nodeValue2152, nodeValue2157, nodeValue2249, nodeValue3591, nodeValue4075]

theorem reindexCheck2162 : Integer.Sparse.reindex keyMap MixedData.row2162 = numericRow2162 := by decide +kernel

theorem numericCheck2162 (x : Master → ℝ) : Integer.Sparse.eval numericRow2162 x =
    (1 : ℝ) * reducedSource2162 x := by
  norm_num [numericRow2162, reducedSource2162, Integer.Sparse.eval, Sparse.eval, nodeValue2154, nodeValue2157, nodeValue2158, nodeValue2166, nodeValue2272, nodeValue3595, nodeValue4075]

theorem reindexCheck2163 : Integer.Sparse.reindex keyMap MixedData.row2163 = numericRow2163 := by decide +kernel

theorem numericCheck2163 (x : Master → ℝ) : Integer.Sparse.eval numericRow2163 x =
    (1 : ℝ) * reducedSource2163 x := by
  norm_num [numericRow2163, reducedSource2163, Integer.Sparse.eval, Sparse.eval, nodeValue2148, nodeValue2152, nodeValue2166, nodeValue2257, nodeValue3592, nodeValue4075]

theorem reindexCheck2164 : Integer.Sparse.reindex keyMap MixedData.row2164 = numericRow2164 := by decide +kernel

theorem numericCheck2164 (x : Master → ℝ) : Integer.Sparse.eval numericRow2164 x =
    (1 : ℝ) * reducedSource2164 x := by
  norm_num [numericRow2164, reducedSource2164, Integer.Sparse.eval, Sparse.eval, nodeValue2658, nodeValue3406, nodeValue3412, nodeValue3417, nodeValue3591, nodeValue4075]

theorem reindexCheck2165 : Integer.Sparse.reindex keyMap MixedData.row2165 = numericRow2165 := by decide +kernel

theorem numericCheck2165 (x : Master → ℝ) : Integer.Sparse.eval numericRow2165 x =
    (1 : ℝ) * reducedSource2165 x := by
  norm_num [numericRow2165, reducedSource2165, Integer.Sparse.eval, Sparse.eval, nodeValue2182, nodeValue3455, nodeValue4077]

theorem reindexCheck2167 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2167)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow1) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2160 (mixedVector B) = 0 := by
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2748, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2165, h2186, h3420, h3457, h3510, h4074, reducedSource2160] using sourceEq2748 B hB

theorem rowSound2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2160, numericCheck2160, reducedZero2160 B hB hF, mul_zero]

theorem reducedZero2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2161 (mixedVector B) = 0 := by
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2144, h2146, h2152, h2157, h2249, h3591, h4075, reducedSource2161] using sourceEq2756 B hB

theorem rowSound2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2161, numericCheck2161, reducedZero2161 B hB hF, mul_zero]

theorem reducedZero2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2162 (mixedVector B) = 0 := by
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2757, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2154, h2157, h2158, h2166, h2272, h3595, h4075, reducedSource2162] using sourceEq2757 B hB

theorem rowSound2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2162, numericCheck2162, reducedZero2162 B hB hF, mul_zero]

theorem reducedZero2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2163 (mixedVector B) = 0 := by
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h3592 : mixedVector B (Sum.inr 3592) = Sparse.eval nodeValue3592 (mixedVector B) := by
    change mixedMoment B node3592 node3592Labels = _
    exact sound3592 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2758, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2148, h2152, h2166, h2257, h3592, h4075, reducedSource2163] using sourceEq2758 B hB

theorem rowSound2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2163 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2163, numericCheck2163, reducedZero2163 B hB hF, mul_zero]

theorem reducedZero2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2164 (mixedVector B) = 0 := by
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2759, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2658, h3406, h3412, h3417, h3591, h4075, reducedSource2164] using sourceEq2759 B hB

theorem rowSound2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2164, numericCheck2164, reducedZero2164 B hB hF, mul_zero]

theorem reducedZero2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2165 (mixedVector B) = 0 := by
  have h2182 : mixedVector B (Sum.inr 2182) = Sparse.eval nodeValue2182 (mixedVector B) := by
    change mixedMoment B node2182 node2182Labels = _
    exact sound2182 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  simpa only [sourceForm2766, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2182, h3455, h4077, reducedSource2165] using sourceEq2766 B hB

theorem rowSound2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2165 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2165, numericCheck2165, reducedZero2165 B hB hF, mul_zero]

theorem rowSound2167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2167 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2167, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow1 (fun _ hH => PairSemantics.boundarySound1 hH)

theorem sourceRowsAt2160 : MixedData.sourceRows (2160 : Fin 2425) =
    MixedData.row2160 := by decide +kernel

theorem sourceRowsAt2161 : MixedData.sourceRows (2161 : Fin 2425) =
    MixedData.row2161 := by decide +kernel

theorem sourceRowsAt2162 : MixedData.sourceRows (2162 : Fin 2425) =
    MixedData.row2162 := by decide +kernel

theorem sourceRowsAt2163 : MixedData.sourceRows (2163 : Fin 2425) =
    MixedData.row2163 := by decide +kernel

theorem sourceRowsAt2164 : MixedData.sourceRows (2164 : Fin 2425) =
    MixedData.row2164 := by decide +kernel

theorem sourceRowsAt2165 : MixedData.sourceRows (2165 : Fin 2425) =
    MixedData.row2165 := by decide +kernel

theorem sourceRowsAt2166 : MixedData.sourceRows (2166 : Fin 2425) =
    MixedData.row2166 := by decide +kernel

theorem sourceRowsAt2167 : MixedData.sourceRows (2167 : Fin 2425) =
    MixedData.row2167 := by decide +kernel

theorem sourceRowsAt2168 : MixedData.sourceRows (2168 : Fin 2425) =
    MixedData.row2168 := by decide +kernel

theorem sourceRowsAt2169 : MixedData.sourceRows (2169 : Fin 2425) =
    MixedData.row2169 := by decide +kernel

theorem sourceRowsAt2170 : MixedData.sourceRows (2170 : Fin 2425) =
    MixedData.row2170 := by decide +kernel

theorem sourceRowsAt2171 : MixedData.sourceRows (2171 : Fin 2425) =
    MixedData.row2171 := by decide +kernel

theorem sourceRowsAt2172 : MixedData.sourceRows (2172 : Fin 2425) =
    MixedData.row2172 := by decide +kernel

theorem sourceRowsAt2173 : MixedData.sourceRows (2173 : Fin 2425) =
    MixedData.row2173 := by decide +kernel

theorem sourceRowsAt2174 : MixedData.sourceRows (2174 : Fin 2425) =
    MixedData.row2174 := by decide +kernel

theorem sourceRowsAt2175 : MixedData.sourceRows (2175 : Fin 2425) =
    MixedData.row2175 := by decide +kernel

theorem chunkSound135_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 135) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2160 ∨ k.val = 2161 ∨ k.val = 2162 ∨ k.val = 2163 ∨ k.val = 2164 ∨ k.val = 2165 ∨ k.val = 2166 ∨ k.val = 2167 ∨ k.val = 2168 ∨ k.val = 2169 ∨ k.val = 2170 ∨ k.val = 2171 ∨ k.val = 2172 ∨ k.val = 2173 ∨ k.val = 2174 ∨ k.val = 2175 := by omega
  rcases heq with h2160 | h2161 | h2162 | h2163 | h2164 | h2165 | h2166 | h2167 | h2168 | h2169 | h2170 | h2171 | h2172 | h2173 | h2174 | h2175
  · have he : k = (2160 : Fin 2425) := Fin.ext h2160
    subst k
    rw [sourceRowsAt2160]
    exact rowSound2160 B hB hF
  · have he : k = (2161 : Fin 2425) := Fin.ext h2161
    subst k
    rw [sourceRowsAt2161]
    exact rowSound2161 B hB hF
  · have he : k = (2162 : Fin 2425) := Fin.ext h2162
    subst k
    rw [sourceRowsAt2162]
    exact rowSound2162 B hB hF
  · have he : k = (2163 : Fin 2425) := Fin.ext h2163
    subst k
    rw [sourceRowsAt2163]
    exact rowSound2163 B hB hF
  · have he : k = (2164 : Fin 2425) := Fin.ext h2164
    subst k
    rw [sourceRowsAt2164]
    exact rowSound2164 B hB hF
  · have he : k = (2165 : Fin 2425) := Fin.ext h2165
    subst k
    rw [sourceRowsAt2165]
    exact rowSound2165 B hB hF
  · have he : k = (2166 : Fin 2425) := Fin.ext h2166
    subst k
    rw [sourceRowsAt2166]
    exact rowSound2166_e B hB hF
  · have he : k = (2167 : Fin 2425) := Fin.ext h2167
    subst k
    rw [sourceRowsAt2167]
    exact rowSound2167 B hB hF
  · have he : k = (2168 : Fin 2425) := Fin.ext h2168
    subst k
    rw [sourceRowsAt2168]
    exact rowSound2168_e B hB hF
  · have he : k = (2169 : Fin 2425) := Fin.ext h2169
    subst k
    rw [sourceRowsAt2169]
    exact rowSound2169_e B hB hF
  · have he : k = (2170 : Fin 2425) := Fin.ext h2170
    subst k
    rw [sourceRowsAt2170]
    exact rowSound2170_e B hB hF
  · have he : k = (2171 : Fin 2425) := Fin.ext h2171
    subst k
    rw [sourceRowsAt2171]
    exact rowSound2171_e B hB hF
  · have he : k = (2172 : Fin 2425) := Fin.ext h2172
    subst k
    rw [sourceRowsAt2172]
    exact rowSound2172_e B hB hF
  · have he : k = (2173 : Fin 2425) := Fin.ext h2173
    subst k
    rw [sourceRowsAt2173]
    exact rowSound2173_e B hB hF
  · have he : k = (2174 : Fin 2425) := Fin.ext h2174
    subst k
    rw [sourceRowsAt2174]
    exact rowSound2174_e B hB hF
  · have he : k = (2175 : Fin 2425) := Fin.ext h2175
    subst k
    rw [sourceRowsAt2175]
    exact rowSound2175_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e_oai
