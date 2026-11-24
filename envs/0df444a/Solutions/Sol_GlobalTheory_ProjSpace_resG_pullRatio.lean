-- Prove2me | solution 1 for GlobalTheory.ProjSpace.resG_pullRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:37.532801+00:00
-- url     : https://prove2.me/submissions/df3a977c-ccb2-4bfd-8ff4-2fd7c3ae2cca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_resG_appLE

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
variable {φ : Y ⟶ PSpace R N} {W V : Y.Opens} {i j k : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {hj : W ≤ φ ⁻¹ᵁ chart R N j}
namespace GlobalTheory.ProjSpace
theorem _root_.solution (h : V ≤ W) :
    resG Y h (pullRatio φ W i hi j) = pullRatio φ V i (h.trans hi) j :=
  resG_appLE φ hi h _
end GlobalTheory.ProjSpace
