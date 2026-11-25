-- Prove2me | solution 1 for GlobalTheory.ProjSpace.IsCoordFamily.basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:24.600091+00:00
-- url     : https://prove2.me/submissions/f83317ea-919d-4a46-b67f-5de95c760f32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul


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
open GlobalTheory.ProjSpace.IsCoordFamily
variable {U : Fin (N + 1) → Y.Opens} {r : ∀ i, Fin (N + 1) → Γ(Y, U i)} (H : IsCoordFamily U r)
include H
namespace GlobalTheory.ProjSpace.IsCoordFamily
theorem _root_.solution (i j : Fin (N + 1)) : Y.basicOpen (r i j) = U i ⊓ U j := by
  refine le_antisymm (le_inf (Y.basicOpen_le _) (H.basicOpen_le i j)) ?_
  have hu : IsUnit (resG Y (inf_le_left : U i ⊓ U j ≤ U i) (r i j)) :=
    .of_mul_eq_one _ ((H.mul i j i).trans (by rw [H.self, map_one]))
  have := Y.basicOpen_of_isUnit hu
  rw [Scheme.basicOpen_res] at this
  exact this.ge.trans inf_le_right
end GlobalTheory.ProjSpace.IsCoordFamily
