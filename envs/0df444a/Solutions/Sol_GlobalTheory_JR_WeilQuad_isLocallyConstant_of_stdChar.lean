-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.isLocallyConstant_of_stdChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:17.21807+00:00
-- url     : https://prove2.me/submissions/9b7f2a2f-d9fe-45ff-adf2-25225da326ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  filter_upwards [Metric.closedBall_mem_nhds a one_pos] with b hb
  have h1 : ψ (b - a) = 1 := hψ.1 _ (by simpa [Metric.mem_closedBall, dist_eq_norm] using hb)
  calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
    _ = ψ a := by rw [AddChar.map_add_eq_mul, h1, mul_one]
end GlobalTheory.JR.WeilQuad
