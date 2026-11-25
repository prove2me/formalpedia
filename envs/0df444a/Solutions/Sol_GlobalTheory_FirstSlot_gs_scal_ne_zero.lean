-- Prove2me | solution 1 for GlobalTheory.FirstSlot.gs_scal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:44:51.670268+00:00
-- url     : https://prove2.me/submissions/b608ff0e-846e-4978-9272-3587ed43f668

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionFirstVariable
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
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
open GlobalTheory.FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FirstSlot
theorem _root_.solution {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Y) {r : R}
    (hr : r ≠ 0) : gs (𝟙 _) z ⊤ (scal (q ≫ jK R) r) ≠ 0 := by
  have h2 : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
    have e := congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have h3 : scal (q ≫ jK R) r = scal q (algebraMap R (FractionRing R) r) := congrArg q.appTop.hom h2
  have hu : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  rw [h3, gs_eq _ z ⊤ trivial]
  exact ((((hu.map _).map q.appTop.hom).map _).map _).ne_zero
end GlobalTheory.FirstSlot
