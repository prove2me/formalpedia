-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_power_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:26.875552+00:00
-- url     : https://prove2.me/submissions/58a1a68d-2bc8-45a1-a766-f19e99a50430

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sum_le_of_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_C_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_X_mem_intPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → Om l)
    (hr : ∀ s ∈ S, ‖r s‖ ≤ 1) {s₀ : ι} (h₀ : s₀ ∈ S) :
    ∃ k : ℕ, ∏ t ∈ S.erase s₀, ‖r s₀ - r t‖ ≤ ‖∑ s ∈ S, r s ^ k‖ := by
  set P : (Om l)[X] := ∏ t ∈ S.erase s₀, (X - C (r t)) with hP
  have hPi : P ∈ intPoly l := prod_mem fun t ht =>
    sub_mem X_mem_intPoly (C_mem_intPoly (hr t (Finset.mem_of_mem_erase ht)))
  have h1 : ∑ s ∈ S, P.eval (r s) = ∏ t ∈ S.erase s₀, (r s₀ - r t) := by
    rw [Finset.sum_eq_single_of_mem s₀ h₀]
    · simp [hP, eval_prod]
    · intro s hs hne
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, hs⟩) (by simp)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (P.natDegree + 1))
    (fun k => ‖∑ s ∈ S, r s ^ k‖) ⟨0, by simp⟩
  refine ⟨k, ?_⟩
  rw [← norm_prod, ← h1]
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine norm_sum_le_of_le _ _ (norm_nonneg _) fun n hn => ?_
  rw [← Finset.mul_sum, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (mem_intPoly.1 hPi n)).trans (hk n hn)
end GlobalTheory.Cyc.DiffSmall
