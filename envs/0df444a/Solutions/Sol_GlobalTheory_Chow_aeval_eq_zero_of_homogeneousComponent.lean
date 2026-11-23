-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_eq_zero_of_homogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:57.715098+00:00
-- url     : https://prove2.me/submissions/8abe7587-c429-46c7-b9f2-97692e486883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}
namespace GlobalTheory.Chow
theorem _root_.solution {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {ξ : σ → G} (h : ∀ n, aeval ξ (homogeneousComponent n g) = 0) :
    aeval ξ g = 0 := by
  rw [← sum_homogeneousComponent g, map_sum]
  exact Finset.sum_eq_zero fun n _ => h n
end GlobalTheory.Chow
