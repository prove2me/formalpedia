-- Prove2me | solution 1 for GlobalTheory.latCont_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:45.370861+00:00
-- url     : https://prove2.me/submissions/24d0dca7-91a9-40fa-9eca-05613a0861b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedAddCommGroup E] (H : AddSubgroup E) (r : ℝ) (hr : 0 < r)
    (h : ∀ z ∈ H, ‖z‖ < r → z = 0) : DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_zero
  have e : ({0} : Set H) = Subtype.val ⁻¹' Metric.ball (0 : E) r := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hr
    · intro hz
      have := h z z.2 hz
      simpa using this
  rw [e]
  exact Metric.isOpen_ball.preimage continuous_subtype_val
end GlobalTheory
