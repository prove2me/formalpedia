-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.isLocallyConstant_char_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:23.796861+00:00
-- url     : https://prove2.me/submissions/ac2f5c7f-b165-4e55-8b2b-c1fa2a7ebfba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd
  have hχ : IsOpen (χ.ker : Set (GL n k)) := hμ.preimage GeneralLinearGroup.continuous_det
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e
end GlobalTheory.GodementJacquet
