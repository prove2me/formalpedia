-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.natDegree_originPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:45.520232+00:00
-- url     : https://prove2.me/submissions/b8110367-f15d-4ad3-9571-81778671bb76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Polynomial
open scoped Polynomial.Bivariate
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution [Nontrivial R] : (originPolynomial W).natDegree = 3 := by
  unfold originPolynomial
  compute_degree!
end GlobalTheory.WeierstrassCurve
