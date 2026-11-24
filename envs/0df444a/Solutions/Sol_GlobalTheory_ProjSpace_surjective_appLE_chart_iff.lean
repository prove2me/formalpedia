-- Prove2me | solution 1 for GlobalTheory.ProjSpace.surjective_appLE_chart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:29:48.878198+00:00
-- url     : https://prove2.me/submissions/bb787978-aedc-4721-9ddb-3ab2b6cf5643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_aeval_ratio_surjective


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
theorem _root_.solution {φ : Y ⟶ PSpace R N} {W : Y.Opens} {i : Fin (N + 1)}
    (hi : W ≤ φ ⁻¹ᵁ chart R N i) :
    Function.Surjective (φ.appLE (chart R N i) W hi).hom ↔
      Function.Surjective (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) W).hom (pullRatio φ W i hi)) := by
  rw [← appLE_comp_aeval_ratio]
  exact (Function.Surjective.of_comp_iff _ (aeval_ratio_surjective R N i)).symm
end GlobalTheory.ProjSpace
