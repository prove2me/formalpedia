-- Prove2me | solution 1 for GlobalTheory.RealWeil.Intertw.eq_of_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:14.376873+00:00
-- url     : https://prove2.me/submissions/35a7b7bf-0118-4227-9032-42b8127f97ce

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
theorem _root_.solution {c c' : ℂ} {F : EuclideanSpace ℝ l → ℂ} {x : EuclideanSpace ℝ l} (hx : F x ≠ 0)
    (h : c • F = c' • F) : c = c' := by
  have := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this
end GlobalTheory.RealWeil.Intertw
