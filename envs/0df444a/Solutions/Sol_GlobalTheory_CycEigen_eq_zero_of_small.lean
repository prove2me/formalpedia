-- Prove2me | solution 1 for GlobalTheory.CycEigen.eq_zero_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:44:18.013801+00:00
-- url     : https://prove2.me/submissions/6c77766b-cde4-4588-932a-b94d18082e70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Theorems.Thm_GlobalTheory_CycEigen_norm_mulVec_le
import Theorems.Thm_GlobalTheory_CycEigen_mulVec_mem
import Theorems.Thm_GlobalTheory_CycEigen_map_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycEigen
theorem _root_.solution {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (O : Set C)
    (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X) (T : C → C) (hTX : ∀ x ∈ X, T x ∈ X)
    (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hBO : ∀ a b, B a b ∈ O) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : y = B.mulVec fun a => T (y a)) : y = 0 := by
  have hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X := fun a b => hOX _ (hBO a b)
  have h1 : ∀ (n : ℕ) (z : Fin r → C), (∀ a, z a ∈ X) →
      (∀ a, B.mulVec^[n] z a ∈ X) ∧ ‖B.mulVec^[n] z‖ ≤ c ^ n ∧
        (fun a => T (B.mulVec^[n] z a)) = B.mulVec^[n] fun a => T (z a) := by
    intro n z hz
    induction n with
    | zero => exact ⟨hz, (pi_norm_le_iff_of_nonneg (by simp)).2 fun a => by
        simpa using hX1 _ (hz a), rfl⟩
    | succ n ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      simp only [Function.iterate_succ_apply']
      refine ⟨mulVec_mem X B hBX _ i1, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_, ?_⟩
      · rw [pow_succ']
        exact (norm_mulVec_le B hc hB _ a).trans (mul_le_mul_of_nonneg_left i2 hc)
      · rw [map_mulVec X O hOX T hadd hlin B hBO _ i1, i3]
  have h2 : ∀ n : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ y = B.mulVec^[n] z := by
    intro n
    induction n with
    | zero => exact ⟨y, hy, rfl⟩
    | succ n ih =>
      obtain ⟨z, hz, e⟩ := ih
      refine ⟨fun a => T (z a), fun a => hTX _ (hz a), ?_⟩
      rw [Function.iterate_succ_apply', ← (h1 n z hz).2.2, ← e]
      exact h
  have h3 : ∀ n : ℕ, ‖y‖ ≤ c ^ n := fun n => by
    obtain ⟨z, hz, e⟩ := h2 n
    rw [e]; exact (h1 n z hz).2.1
  exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) h3)
end GlobalTheory.CycEigen
