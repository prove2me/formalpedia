-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:30.624796+00:00
-- url     : https://prove2.me/submissions/413da581-35e8-4529-b5d9-8d23ed10ae01

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}
omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] [NormedSpace ℂ W]
namespace GlobalTheory.ThetaRational
theorem _root_.solution (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0) :
    ∃ ε > 0, ∀ k ∈ K, ε ≤ ‖θ k‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨k, -, hk⟩ := hK.exists_isMinOn hne hθ.norm.continuousOn
  exact ⟨‖θ k‖, norm_pos_iff.2 (hN k), fun x hx => hk hx⟩
end GlobalTheory.ThetaRational
