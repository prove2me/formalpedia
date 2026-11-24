-- Prove2me | solution 1 for GlobalTheory.ProjSpace.IsCoordFamily.pullRatio_toHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:34.332055+00:00
-- url     : https://prove2.me/submissions/72cba6fb-a80e-4a88-81cc-3b6c3e77a239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_pullRatio_of_eq

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
theorem _root_.solution (f : Y ⟶ Sp R) (i j : Fin (N + 1)) :
    pullRatio (H.toHom f) (U i) i (H.le_toHom_preimage f i) j = r i j := by
  refine (ConcreteCategory.bijective_of_isIso ((U i).ι.appLE (U i) ⊤ (U i).ι_preimage_self.ge)).1 ?_
  refine (appLE_pullRatio _ _).trans ?_
  refine (pullRatio_of_eq ((H.ι_toHom f i).trans (Category.id_comp _).symm) _
    (ofCoords_preimage f _ i _ (𝟙 _))).trans ?_
  exact pullRatio_comp_ofCoords f (U i) i (H.self i) (𝟙 _) ⊤ _ (U i).ι_preimage_self.ge j
end GlobalTheory.ProjSpace.IsCoordFamily
