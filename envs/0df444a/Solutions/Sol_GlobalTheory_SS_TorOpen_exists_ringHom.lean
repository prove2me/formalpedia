-- Prove2me | solution 1 for GlobalTheory.SS.TorOpen.exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:09.270027+00:00
-- url     : https://prove2.me/submissions/b239482f-dcec-4799-a841-f9feb438b3f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMultiplicativeGroupOpenNonvanishingPolynom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace GlobalTheory.SS.TorOpen
theorem _root_.solution (k : Type) [Field k] (q : Polynomial k) :
    ∃ ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* Localization.Away (Polynomial.X * q),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) ∧
      ψ.comp (algebraMap k _) = algebraMap k _ ∧
      ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
  let L := Localization.Away (Polynomial.X * q)
  have hu : IsUnit (algebraMap (Polynomial k) L Polynomial.X) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := L) (Polynomial.X * q)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  let ψ' : LaurentPolynomial k →+* L := IsLocalization.Away.lift (Polynomial.X : Polynomial k) hu
  have hψ : ψ'.comp (algebraMap (Polynomial k) _) = algebraMap _ _ :=
    IsLocalization.Away.lift_comp _ hu
  let e : AddMonoidAlgebra k (ULift.{0} ℤ) ≃ₐ[k] LaurentPolynomial k :=
    AddMonoidAlgebra.domCongr k k AddEquiv.ulift
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ')) := by
    have a1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) :=
      IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial k)
    have a2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ') ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact IsOpenImmersion.of_isLocalization (Polynomial.X * q)
    exact IsOpenImmersion.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k))))
  refine ⟨ψ'.comp e.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  · ext c
    have : e (algebraMap k _ c) = algebraMap (Polynomial k) _ (algebraMap k _ c) := by
      rw [e.commutes]; simp
    change ψ' (e (algebraMap k _ c)) = _
    rw [this, ← RingHom.comp_apply, hψ, ← IsScalarTower.algebraMap_apply]
  · have : e (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
      simp [e]; rfl
    change ψ' (e _) = _
    rw [this, ← RingHom.comp_apply, hψ]
end GlobalTheory.SS.TorOpen
