-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.rhoSch_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:25.808989+00:00
-- url     : https://prove2.me/submissions/ac5a0fc5-99da-42b9-8b3e-ce6ec34ffb6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_hasTemperateGrowth_phase
import Theorems.Thm_GlobalTheory_PhaseLipschitz_hasTemperateGrowth_phase
import Theorems.Thm_GlobalTheory_RealWeil_coe_rhoSch
import Theorems.Thm_GlobalTheory_RealWeil_phase_eq_eChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by
  ext x
  rw [coe_rhoSch, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, rhoFun, phase_eq_eChar, sub_neg_eq_add]
  simp
end GlobalTheory.RealWeil.SchrFamily
