-- Prove2me | solution 1 for GlobalTheory.RealWeil.Intertw.sympl_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:32.285313+00:00
-- url     : https://prove2.me/submissions/86362c50-6ce0-46bd-9312-7054447c13f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
import Theorems.Thm_GlobalTheory_RealWeil_pPart_smul
import Theorems.Thm_GlobalTheory_RealWeil_qPart_smul
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.Intertw
theorem _root_.solution (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]
  ring
end GlobalTheory.RealWeil.Intertw
