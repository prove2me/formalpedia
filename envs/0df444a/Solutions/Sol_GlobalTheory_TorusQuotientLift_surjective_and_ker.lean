-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.surjective_and_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:31.455824+00:00
-- url     : https://prove2.me/submissions/32f5b1c0-db2c-4d34-9706-191b6adbb32f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Theorems.Thm_GlobalTheory_PrimeSection_ker_eq_map_of_isPushout
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorusQuotientLift
theorem _root_.solution {A : Type} [CommRing A] {J : Ideal A} {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec (CommRingCat.of (A ⧸ J))}
    (h : IsPullback i f' f (red J)) {U : Y.Opens} (hU : IsAffineOpen U) {U' : Z.Opens} (e : i ⁻¹ᵁ U = U') :
    Function.Surjective (i.appLE U U' e.ge).hom ∧ RingHom.ker (i.appLE U U' e.ge).hom = J.map (baseMap f U) := by
  subst e
  have : IsClosedImmersion i := MorphismProperty.of_isPullback h.flip inferInstance
  rw [Scheme.Hom.appLE_eq_app]
  refine ⟨i.app_surjective U hU, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (i.app U)
      ((Scheme.ΓSpecIso (.of (A ⧸ J))).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [PrimeSection.ker_eq_map_of_isPushout hpo' Ideal.Quotient.mk_surjective]
  exact congrArg (Ideal.map _) Ideal.mk_ker
end GlobalTheory.TorusQuotientLift
