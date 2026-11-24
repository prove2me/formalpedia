-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.coe_smulLeft_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:41.4388+00:00
-- url     : https://prove2.me/submissions/a4eb5649-fc29-4cf1-abef-f21d98c2ddc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_PhaseLipschitz_eChar_sub_one_eq
import Theorems.Thm_GlobalTheory_PhaseLipschitz_hasTemperateGrowth_phase
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_hasTemperateGrowth_phase


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz
namespace GlobalTheory.PhaseLipschitz
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring
end GlobalTheory.PhaseLipschitz
