-- Prove2me | solution 1 for GlobalTheory.StdChar.locConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:43.143949+00:00
-- url     : https://prove2.me/submissions/af4a861f-d885-48a3-a68b-e19e9bcb6fb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.StdChar
theorem _root_.solution [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun x' hx' => ?_⟩
  have h : ψ (x' - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx').le)
  calc ψ x' = ψ (x + (x' - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h, mul_one]
end GlobalTheory.StdChar
