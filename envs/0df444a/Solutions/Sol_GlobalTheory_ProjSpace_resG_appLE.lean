-- Prove2me | solution 1 for GlobalTheory.ProjSpace.resG_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:08.254049+00:00
-- url     : https://prove2.me/submissions/fd8b2360-a7ca-487c-bf68-62a98b798970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}
namespace GlobalTheory.ProjSpace
theorem _root_.solution (g : Z ⟶ Y) {U : Y.Opens} {V W : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) (h' : W ≤ V)
    (a : Γ(Y, U)) :
    resG Z h' ((g.appLE U V h).hom a) = (g.appLE U W (h'.trans h)).hom a :=
  congrArg (fun φ => φ.hom a) (g.appLE_map h (homOfLE h').op)
end GlobalTheory.ProjSpace
