-- Prove2me | solution 1 for GlobalTheory.RealWeil.Intertw.coe_smul_sch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:27.42203+00:00
-- url     : https://prove2.me/submissions/52c18798-6f95-4db4-8e91-ff5865da3ac1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
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
theorem _root_.solution (c : ℂ) (f : Sch l) : ⇑(c • f) = c • ⇑f := by
  funext x
  simp
end GlobalTheory.RealWeil.Intertw
