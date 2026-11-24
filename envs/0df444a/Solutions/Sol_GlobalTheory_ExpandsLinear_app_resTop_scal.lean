-- Prove2me | solution 1 for GlobalTheory.ExpandsLinear.app_resTop_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:24.399415+00:00
-- url     : https://prove2.me/submissions/42170475-7e1d-4420-9cfe-6a0c858073ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ExpandsLinear
namespace GlobalTheory.ExpandsLinear
theorem _root_.solution {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl
end GlobalTheory.ExpandsLinear
