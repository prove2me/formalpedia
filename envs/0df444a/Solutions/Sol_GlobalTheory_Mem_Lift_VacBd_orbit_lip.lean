-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacBd.orbit_lip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:56.75068+00:00
-- url     : https://prove2.me/submissions/06e31e2f-bf3a-440f-8183-e24e2cd5627f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacBd
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.VacBd
theorem _root_.solution (h : IsHeis om ρ) {f : B} (hf : Sm ρ f) : ∃ C : ℝ, ∀ z, ‖ρ z f - f‖ ≤ C * ‖z‖ := by
  have hd := (ContDiff.differentiable hf (by simp) 0).hasFDerivAt.isBigO_sub
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  obtain ⟨δ, hδ, hC⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C + 2 * ‖f‖ / δ, fun z => ?_⟩
  have h0 : 0 ≤ 2 * ‖f‖ / δ * ‖z‖ := by positivity
  have h1 : 0 ≤ C * ‖z‖ := by positivity
  rw [add_mul]
  by_cases hz : ‖z‖ < δ
  · have := hC (y := z) (by simpa using hz)
    simp only [h.1, sub_zero] at this
    linarith
  · have h2 : ‖ρ z f - f‖ ≤ 2 * ‖f‖ := by
      have := norm_sub_le (ρ z f) f
      rw [h.2.2.1] at this
      linarith
    have h3 : 2 * ‖f‖ ≤ 2 * ‖f‖ / δ * ‖z‖ := by
      calc 2 * ‖f‖ = 2 * ‖f‖ / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (not_lt.1 hz) (by positivity)
    linarith
end GlobalTheory.Mem.Lift.VacBd
