-- Prove2me | solution 1 for GlobalTheory.ProjSpace.isCoordFamily_pullRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:06.527145+00:00
-- url     : https://prove2.me/submissions/fcc87865-c471-4f62-bc6f-c19bd63af5f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_resG_pullRatio
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
namespace GlobalTheory.ProjSpace
theorem _root_.solution (φ : Y ⟶ PSpace R N) :
    IsCoordFamily (fun i => φ ⁻¹ᵁ chart R N i) (fun i => pullRatio φ _ i le_rfl) where
  cover := by rw [← Scheme.Hom.preimage_iSup, iSup_chart]; rfl
  self _ := pullRatio_self
  mul i j k := by rw [resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  basicOpen_le _ _ := basicOpen_pullRatio.le.trans inf_le_right
end GlobalTheory.ProjSpace
