-- Prove2me | solution 1 for GlobalTheory.FieldChange.isUnit_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:56:31.65472+00:00
-- url     : https://prove2.me/submissions/0f3bf6b5-f2fc-4adc-8f8d-b7538257d903

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
open GlobalTheory.FieldChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldChange
theorem _root_.solution {c : R} (hc : c ≠ 0) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) :
    IsUnit (gs r z ⊤ (scal (DegPre.BF D F).hom c)) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.assoc]; exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  have hu : IsUnit (scal (jK R) c) := by
    have n := congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    have hc' : IsUnit (algebraMap R (FractionRing R) c) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hc)
    exact (congrArg IsUnit n).mp (hc'.map _)
  rw [e, gs_eq _ _ ⊤ (by trivial)]
  exact ((hu.map ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F).appTop.hom).map _).map _
end GlobalTheory.FieldChange
