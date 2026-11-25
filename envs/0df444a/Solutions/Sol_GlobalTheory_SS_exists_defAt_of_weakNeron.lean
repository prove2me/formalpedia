-- Prove2me | solution 1 for GlobalTheory.SS.exists_defAt_of_weakNeron
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:23.64013+00:00
-- url     : https://prove2.me/submissions/7ef4cef9-90fc-42ba-9d15-78e6ff7d205c

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
import Theorems.Thm_GlobalTheory_SS_WeakNeronDef_fromSpecStalk_comp
import Theorems.Thm_GlobalTheory_SS_WeakNeronDef_isDominant_fromSpecStalk
import Theorems.Thm_GlobalTheory_SS_WeakNeronDef_isPullback_j
import Theorems.Thm_GlobalTheory_SS_WeakNeronDef_exists_dvr_point
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_isLocalization_away
import Theorems.Thm_GlobalTheory_DvrModel_isOpenImmersion_generic
import Theorems.Thm_GlobalTheory_SS_Model_j_hom
import Theorems.Thm_GlobalTheory_isDominant_spMap_of_isFractionRing
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
open GlobalTheory GlobalTheory.SS
open WeakNeronDef
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away K hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm
end GlobalTheory.SS
