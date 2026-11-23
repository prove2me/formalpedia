-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:31.01544+00:00
-- url     : https://prove2.me/submissions/f6d557fe-dcea-4895-976d-f88f9de8f006

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
omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V]
namespace GlobalTheory.ThetaRational
theorem _root_.solution
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z) (e : ℂ × V) :
    ∃ e' : ℂ × V, e'.2 ∈ K ∧ e'.1 • θ e'.2 = e.1 • θ e.2 ∧ e'.1 ^ d * f e'.2 = e.1 ^ d * f e.2 := by
  obtain ⟨k, hk, hl⟩ := hP e.2
  obtain ⟨κ, -, hκ⟩ := hL _ hl
  obtain ⟨-, h1, h2⟩ := hκ k
  rw [add_sub_cancel] at h1 h2
  refine ⟨(e.1 * κ k, k), hk, ?_, ?_⟩
  · rw [h1, mul_smul]
  · rw [h2, mul_pow, mul_assoc]
end GlobalTheory.ThetaRational
