-- Prove2me | solution 1 for GlobalTheory.ProjSpace.pullRatio_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:58.607647+00:00
-- url     : https://prove2.me/submissions/d8651330-9977-43c5-aa5e-c318c78999a2

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
variable {φ : Y ⟶ PSpace R N} {W V : Y.Opens} {i j k : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {hj : W ≤ φ ⁻¹ᵁ chart R N j}
namespace GlobalTheory.ProjSpace
theorem _root_.solution {ψ : Y ⟶ PSpace R N} (h : φ = ψ) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (hi' : W ≤ ψ ⁻¹ᵁ chart R N i) : pullRatio φ W i hi j = pullRatio ψ W i hi' j := by
  subst h
  rfl
end GlobalTheory.ProjSpace
