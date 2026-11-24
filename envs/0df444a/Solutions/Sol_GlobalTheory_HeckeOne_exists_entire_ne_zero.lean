-- Prove2me | solution 1 for GlobalTheory.HeckeOne.exists_entire_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:49.159947+00:00
-- url     : https://prove2.me/submissions/828d671d-69d0-4d3f-86ee-5e409fff3b45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_isNormPow_one
import Theorems.Thm_GlobalTheory_HeckeOne_isContAtOne_of_isHeckeL
import Theorems.Thm_GlobalTheory_HeckeOne_IsContAtOne_apply_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.HeckeOne
theorem _root_.solution (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) {χ : HChar K} (hu : χ.IsUnitary)
    (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) : ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ 1 ≠ 0 := by
  obtain ⟨Λ, hΛ⟩ := (H K χ hu).1 hχ
  obtain ⟨Λ', h', h0⟩ := (H K χ hu).2 fun h => hχ ⟨0, h ▸ isNormPow_one⟩
  exact ⟨Λ, hΛ, (isContAtOne_of_isHeckeL hΛ).apply_one_eq h' ▸ h0⟩
end GlobalTheory.HeckeOne
