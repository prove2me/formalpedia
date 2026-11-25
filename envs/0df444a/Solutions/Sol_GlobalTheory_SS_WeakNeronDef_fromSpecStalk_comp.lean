-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronDef.fromSpecStalk_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:23.578808+00:00
-- url     : https://prove2.me/submissions/828280b2-d4ed-46e3-a1f3-224d23298aa8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsModelMapDefinedWeakNeronFamily
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronDef
namespace GlobalTheory.SS.WeakNeronDef
theorem _root_.solution {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp
end GlobalTheory.SS.WeakNeronDef
