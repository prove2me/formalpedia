-- Prove2me | solution 1 for GlobalTheory.HolHom.eq_of_isDerivAt_constVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:09.810484+00:00
-- url     : https://prove2.me/submissions/10cd09eb-af48-48d8-8665-a7e82a4c74a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_point_ext
import Theorems.Thm_GlobalTheory_HolHom_exists_affine
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_constVec_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} (h : ∀ z, HolAt c z)
    (h' : ∀ z w, IsDerivAt c z w (constVec (c z))) (z z' : V) : c z = c z' := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ ℂ V
  refine IsLocallyConstant.apply_eq_of_preconnectedSpace ((IsLocallyConstant.iff_eventually_eq c).2 fun x => ?_) z z'
  obtain ⟨P, hP, hx, -⟩ := exists_affine (c x) (U := ⊤) le_top
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h x P hx).1
  filter_upwards [Metric.ball_mem_nhds x hr] with t ht
  refine point_ext hP (hball t ht) hx fun f => ?_
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun t => valAt' (c t) P f)
    (convex_ball x r).isPreconnected (fun s hs => ((h s P (hball s hs)).2 f).differentiableWithinAt)
    (fun s hs => ContinuousLinearMap.ext fun w => isDerivAt_constVec_iff.1 (h' s w) P (hball s hs) f)
    ht (Metric.mem_ball_self hr)
end GlobalTheory.HolHom
