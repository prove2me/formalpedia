-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:38.119228+00:00
-- url     : https://prove2.me/submissions/fca1ca00-4250-47de-81b2-236f0c5fc6de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar


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
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))
end GlobalTheory.PhaseLipschitz
