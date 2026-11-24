-- Prove2me | solution 1 for GlobalTheory.JetOnto.comp_eq_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:24.200752+00:00
-- url     : https://prove2.me/submissions/2d596872-bd5c-42d9-83c2-f7e1a60e9054

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetOnto
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace GlobalTheory.JetOnto
theorem _root_.solution {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] {X : Over (Spec (CommRingCat.of R))} (p : A →ₐ[R] B) (q : B →ₐ[R] C)
    {y y' : sp (R₀ := R) A ⟶ X} (h : spMap p ≫ y = spMap p ≫ y') :
    spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := by
  rw [← spMap_comp, Category.assoc, Category.assoc, h]
end GlobalTheory.JetOnto
