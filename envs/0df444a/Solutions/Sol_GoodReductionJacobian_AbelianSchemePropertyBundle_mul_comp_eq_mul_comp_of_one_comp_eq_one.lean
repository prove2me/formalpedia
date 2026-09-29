-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/92385c1d-3836-57ed-ba22-3ba6f008a168

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace HomOfUnitBody

variable {R : Type u} [CommRing R] {A B : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (M : RelativeGroupLaw R g) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ hψ (M.inv t x) = M.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := M.pointGroup t'
  have h : M.mul t' (schemeHomOverComp ψ hψ (M.inv t x)) (schemeHomOverComp ψ hψ x) = M.one t' := by
    rw [← M.mul_natural t t' ψ hψ, M.inv_mul_cancel, M.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def uPt (u : A ⟶ B) (hu : u ≫ g = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : SchemeHomOver t g :=
  ⟨x.1 ≫ u, by rw [Category.assoc, hu, x.2]⟩

@[scoped simp] theorem uPt_coe (u : A ⟶ B) (hu : u ≫ g = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : (uPt u hu x).1 = x.1 ≫ u := rfl

theorem uPt_natural (u : A ⟶ B) (hu : u ≫ g = f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (uPt u hu x) = uPt u hu (schemeHomOverComp ψ hψ x) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem uPt_one (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    uPt u hu (L.one t) = M.one t := by
  have hL := L.one_natural (𝟙 _) t t (Category.comp_id t)
  have hM := M.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← hL, ← uPt_natural, ← hM]
  congr 1
  exact Subtype.ext hone

def defect (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) : SchemeHomOver t g :=
  M.mul t (uPt u hu (L.mul t P Q)) (M.inv t (M.mul t (uPt u hu P) (uPt u hu Q)))

theorem defect_natural (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (defect L M u hu t P Q) =
      defect L M u hu t' (schemeHomOverComp ψ hψ P) (schemeHomOverComp ψ hψ Q) := by
  unfold defect
  rw [M.mul_natural, inv_natural, M.mul_natural, uPt_natural, uPt_natural, uPt_natural, L.mul_natural]

theorem defect_one_left (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) :
    defect L M u hu t (L.one t) Q = M.one t := by
  unfold defect
  rw [L.one_mul, uPt_one L M u hu hone, M.one_mul, M.mul_inv_cancel]

theorem defect_one_right (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    defect L M u hu t P (L.one t) = M.one t := by
  unfold defect
  rw [L.mul_one, uPt_one L M u hu hone, M.mul_one, M.mul_inv_cancel]

theorem mul_of_defect_eq_one (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f)
    (h : defect L M u hu t P Q = M.one t) :
    uPt u hu (L.mul t P Q) = M.mul t (uPt u hu P) (uPt u hu Q) := by
  letI := M.pointGroup t
  exact mul_inv_eq_one.mp h

noncomputable def P₀ (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (prodStr f f) f := ⟨pullback.fst f f, rfl⟩

noncomputable def Q₀ (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (prodStr f f) f :=
  ⟨pullback.snd f f, pullback.condition.symm⟩

theorem comp_P₀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    schemeHomOverComp (prodPairPt P Q).1 (prodPairPt P Q).2 (P₀ f) = P :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem comp_Q₀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    schemeHomOverComp (prodPairPt P Q).1 (prodPairPt P Q).2 (Q₀ f) = Q :=
  Subtype.ext (pullback.lift_snd _ _ _)

theorem pair_comp_defect (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    (prodPairPt P Q).1 ≫ (defect L M u hu (prodStr f f) (P₀ f) (Q₀ f)).1 = (defect L M u hu t P Q).1 := by
  have h := congrArg Subtype.val
    (defect_natural L M u hu (prodStr f f) t (prodPairPt P Q).1 (prodPairPt P Q).2 (P₀ f) (Q₀ f))
  rw [GoodReductionJacobian.schemeHomOverComp_coe, comp_P₀, comp_Q₀] at h
  exact h

theorem geometricallyReduced (hA : AbelianSchemePropertyBundle R f) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  haveI := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  exact GeometricallyReduced.geometrically_isReduced (f := RelativeGroupLaw.fibreStr f y)

theorem geometricallyConnected (hA : AbelianSchemePropertyBundle R f) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  haveI := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  intro K _ z Z fst snd h
  haveI : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := RelativeGroupLaw.fibreStr f y) z fst snd h
  infer_instance

theorem geometricallyReduced_prodStr (hA : AbelianSchemePropertyBundle R f) :
    GeometricallyReduced (prodStr f f) := by
  haveI := hA.smooth
  haveI := geometricallyReduced hA
  refine ⟨geometrically_iff_of_commRing.mpr fun K _ _ Y fst' snd' hY => ?_⟩
  set ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  haveI : AlgebraicGeometry.IsReduced (pullback f ι) :=
    GeometricallyReduced.geometrically_isReduced (f := f) ι (pullback.fst f ι) (pullback.snd f ι)
      (IsPullback.of_hasPullback f ι)
  haveI : IsLocallyNoetherian (pullback f ι) := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f ι)
  haveI : AlgebraicGeometry.IsReduced (pullback (pullback.fst f f) (pullback.fst f ι)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (pullback.snd (pullback.fst f f) (pullback.fst f ι))
  haveI : AlgebraicGeometry.IsReduced (pullback (pullback.fst f f ≫ f) ι) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso f ι (pullback.fst f f)).inv
  exact isReduced_of_isOpenImmersion (hY.isoPullback).hom

theorem geometricallyConnected_prodStr (hA : AbelianSchemePropertyBundle R f) :
    GeometricallyConnected (prodStr f f) := by
  haveI := hA.smooth
  haveI := geometricallyConnected hA
  exact GeometricallyConnected.comp _ _

theorem surjective_app_prodStr (hA : AbelianSchemePropertyBundle R f) (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Surjective ((prodStr f f).app U) := by
  haveI := hA.proper
  haveI := hA.smooth
  haveI := geometricallyReduced_prodStr hA
  haveI := geometricallyConnected_prodStr hA
  exact (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected (prodStr f f) U).2

theorem isClosedMap_prodStr (hA : AbelianSchemePropertyBundle R f) : IsClosedMap (prodStr f f) := by
  haveI := hA.proper
  exact (prodStr f f).isClosedMap

theorem comp_defect_eq (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    {T : Scheme.{u}} (n : T ⟶ pullback f f) (t : T ⟶ Spec (CommRingCat.of R)) (ht : n ≫ prodStr f f = t) :
    n ≫ (defect L M u hu (prodStr f f) (P₀ f) (Q₀ f)).1 =
      (defect L M u hu t ⟨n ≫ pullback.fst f f, by rw [Category.assoc]; exact ht⟩
        ⟨n ≫ pullback.snd f f, by rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact ht⟩).1 := by
  subst ht
  have hn : (prodPairPt (⟨n ≫ pullback.fst f f, by rw [Category.assoc]⟩ : SchemeHomOver (n ≫ prodStr f f) f)
      ⟨n ≫ pullback.snd f f, by rw [Category.assoc, pullback_snd_comp_eq_prodStr]⟩).1 = n := by
    rw [prodPairPt_coe]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  have h := pair_comp_defect L M u hu (n ≫ prodStr f f)
    ⟨n ≫ pullback.fst f f, by rw [Category.assoc]⟩
    ⟨n ≫ pullback.snd f f, by rw [Category.assoc, pullback_snd_comp_eq_prodStr]⟩
  rw [hn] at h
  exact h

theorem one_coe (M : RelativeGroupLaw R g) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (M.one t).1 = t ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := congrArg Subtype.val (M.one_natural (𝟙 _) t t (Category.comp_id t))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h.symm

theorem geomPoint_comp_defect (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (zbar : Spec (CommRingCat.of k) ⟶ pullback f f) (hz : zbar ≫ prodStr f f = σ) :
    zbar ≫ (defect L M u hu (prodStr f f) (P₀ f) (Q₀ f)).1 = σ ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  haveI := hA.proper
  haveI := hA.smooth
  set D : SchemeHomOver (prodStr f f) g := defect L M u hu (prodStr f f) (P₀ f) (Q₀ f) with hD_def
  have hε : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  have heB : (M.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ g = 𝟙 _ := (M.one (𝟙 (Spec (CommRingCat.of R)))).2

  have hcondA : pullback.fst f σ ≫ f = pullback.snd f σ ≫ σ := pullback.condition
  have hAk : AbelianSchemePropertyBundle k (pullback.snd f σ) := hA.baseChange_of_field σ
  haveI : IsIntegral (pullback f σ) := hAk.isIntegral_of_field
  have hLone : (L.one (pullback.fst f σ ≫ f)).1 =
      pullback.snd f σ ≫ σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    rw [one_coe L, hcondA, Category.assoc]

  have hx₀c : (σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f = 𝟙 _ ≫ σ := by
    rw [Category.assoc, hε, Category.comp_id, Category.id_comp]
  set x₀ : Spec (CommRingCat.of k) ⟶ pullback f σ :=
    pullback.lift (σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (𝟙 _) hx₀c with hx₀_def
  have hx₀ : x₀ ≫ pullback.snd f σ = 𝟙 _ := pullback.lift_snd _ _ _
  have hx₀A : x₀ ≫ pullback.fst f σ = σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    pullback.lift_fst _ _ _
  have hz₀c : (σ ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ g = 𝟙 _ ≫ σ := by
    rw [Category.assoc, heB, Category.comp_id, Category.id_comp]
  set z₀ : Spec (CommRingCat.of k) ⟶ pullback g σ :=
    pullback.lift (σ ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1) (𝟙 _) hz₀c with hz₀_def
  have hz₀ : z₀ ≫ pullback.snd g σ = 𝟙 _ := pullback.lift_snd _ _ _
  have hz₀B : z₀ ≫ pullback.fst g σ = σ ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    pullback.lift_fst _ _ _

  have hξc : (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ) ≫ f =
      (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ) ≫ f := by
    rw [Category.assoc, Category.assoc, hcondA, ← Category.assoc, pullback.condition, Category.assoc]
  set ξ : pullback (pullback.snd f σ) (pullback.snd f σ) ⟶ pullback f f :=
    pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ) hξc with hξ_def
  have hξfst : ξ ≫ pullback.fst f f = pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ :=
    pullback.lift_fst _ _ _
  have hξsnd : ξ ≫ pullback.snd f f = pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ :=
    pullback.lift_snd _ _ _
  have hξstr : ξ ≫ prodStr f f = (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ) ≫ σ := by
    rw [← Category.assoc, hξfst, Category.assoc, Category.assoc, hcondA]

  have hφc : (ξ ≫ D.1) ≫ g = (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ) ≫ σ := by
    rw [Category.assoc, D.2, hξstr]
  set φ : pullback (pullback.snd f σ) (pullback.snd f σ) ⟶ pullback g σ :=
    pullback.lift (ξ ≫ D.1) (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ) hφc
    with hφ_def
  have hφB : φ ≫ pullback.fst g σ = ξ ≫ D.1 := pullback.lift_fst _ _ _
  have hφ : φ ≫ pullback.snd g σ = pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ :=
    pullback.lift_snd _ _ _

  have hslice₁ : ∀ (m : pullback f σ ⟶ pullback (pullback.snd f σ) (pullback.snd f σ)),
      m ≫ pullback.fst (pullback.snd f σ) (pullback.snd f σ) = 𝟙 _ →
      m ≫ pullback.snd (pullback.snd f σ) (pullback.snd f σ) = pullback.snd f σ ≫ x₀ →
      (m ≫ ξ) ≫ D.1 = (pullback.fst f σ ≫ f) ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    intro m hm1 hm2
    have hstr : (m ≫ ξ) ≫ prodStr f f = pullback.fst f σ ≫ f := by
      rw [Category.assoc, hξstr, ← Category.assoc, ← Category.assoc, hm1, Category.id_comp, hcondA]
    rw [hD_def, comp_defect_eq L M u hu (m ≫ ξ) (pullback.fst f σ ≫ f) hstr]
    have hP : (⟨(m ≫ ξ) ≫ pullback.fst f f, by rw [Category.assoc]; exact hstr⟩ :
        SchemeHomOver (pullback.fst f σ ≫ f) f) = ⟨pullback.fst f σ, rfl⟩ := by
      apply Subtype.ext
      show (m ≫ ξ) ≫ pullback.fst f f = pullback.fst f σ
      rw [Category.assoc, hξfst, ← Category.assoc, hm1, Category.id_comp]
    have hQ : (⟨(m ≫ ξ) ≫ pullback.snd f f, by
          rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact hstr⟩ :
        SchemeHomOver (pullback.fst f σ ≫ f) f) = L.one _ := by
      apply Subtype.ext
      show (m ≫ ξ) ≫ pullback.snd f f = (L.one (pullback.fst f σ ≫ f)).1
      rw [hLone, Category.assoc, hξsnd, ← Category.assoc, hm2, Category.assoc, hx₀A]
    rw [hP, hQ, defect_one_right L M u hu hone, one_coe M]

  have hslice₂ : ∀ (m : pullback f σ ⟶ pullback (pullback.snd f σ) (pullback.snd f σ)),
      m ≫ pullback.fst (pullback.snd f σ) (pullback.snd f σ) = pullback.snd f σ ≫ x₀ →
      m ≫ pullback.snd (pullback.snd f σ) (pullback.snd f σ) = 𝟙 _ →
      (m ≫ ξ) ≫ D.1 = (pullback.fst f σ ≫ f) ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    intro m hm1 hm2
    have hstr : (m ≫ ξ) ≫ prodStr f f = pullback.fst f σ ≫ f := by
      rw [Category.assoc, ← pullback_snd_comp_eq_prodStr, ← Category.assoc ξ, hξsnd, ← Category.assoc,
        ← Category.assoc, hm2, Category.id_comp]
    rw [hD_def, comp_defect_eq L M u hu (m ≫ ξ) (pullback.fst f σ ≫ f) hstr]
    have hQ : (⟨(m ≫ ξ) ≫ pullback.snd f f, by
          rw [Category.assoc, pullback_snd_comp_eq_prodStr]; exact hstr⟩ :
        SchemeHomOver (pullback.fst f σ ≫ f) f) = ⟨pullback.fst f σ, rfl⟩ := by
      apply Subtype.ext
      show (m ≫ ξ) ≫ pullback.snd f f = pullback.fst f σ
      rw [Category.assoc, hξsnd, ← Category.assoc, hm2, Category.id_comp]
    have hP : (⟨(m ≫ ξ) ≫ pullback.fst f f, by rw [Category.assoc]; exact hstr⟩ :
        SchemeHomOver (pullback.fst f σ ≫ f) f) = L.one _ := by
      apply Subtype.ext
      show (m ≫ ξ) ≫ pullback.fst f f = (L.one (pullback.fst f σ ≫ f)).1
      rw [hLone, Category.assoc, hξfst, ← Category.assoc, hm1, Category.assoc, hx₀A]
    rw [hP, hQ, defect_one_left L M u hu hone, one_coe M]

  have hm₁c : 𝟙 (pullback f σ) ≫ pullback.snd f σ = (pullback.snd f σ ≫ x₀) ≫ pullback.snd f σ := by
    rw [Category.id_comp, Category.assoc, hx₀, Category.comp_id]
  have hconst : pullback.lift (𝟙 (pullback f σ)) (pullback.snd f σ ≫ x₀) hm₁c ≫ φ = pullback.snd f σ ≫ z₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφB, ← Category.assoc, Category.assoc _ z₀, hz₀B,
        hslice₁ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), hcondA, Category.assoc]
    · rw [Category.assoc, hφ, Category.assoc, hz₀, Category.comp_id, ← Category.assoc, pullback.lift_fst,
        Category.id_comp]
  have hfac := AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper k (pullback.snd f σ)
    (pullback.snd f σ) inferInstance (pullback.snd g σ) x₀ hx₀ x₀ hx₀ φ hφ z₀ hconst
  have hm₂c : (pullback.snd f σ ≫ x₀) ≫ pullback.snd f σ = 𝟙 (pullback f σ) ≫ pullback.snd f σ := by
    rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp]
  have hχ : (pullback.lift (pullback.snd f σ ≫ x₀) (𝟙 (pullback f σ)) hm₂c ≫ φ) ≫ pullback.fst g σ =
      (pullback.fst f σ ≫ f) ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    rw [Category.assoc, hφB, ← Category.assoc, hslice₂ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)]

  have ha : (zbar ≫ pullback.fst f f) ≫ f = 𝟙 _ ≫ σ := by
    rw [Category.id_comp, Category.assoc]; exact hz
  have hb : (zbar ≫ pullback.snd f f) ≫ f = 𝟙 _ ≫ σ := by
    rw [Category.id_comp, Category.assoc, pullback_snd_comp_eq_prodStr]; exact hz
  have hab : pullback.lift (zbar ≫ pullback.fst f f) (𝟙 _) ha ≫ pullback.snd f σ =
      pullback.lift (zbar ≫ pullback.snd f f) (𝟙 _) hb ≫ pullback.snd f σ := by
    rw [pullback.lift_snd, pullback.lift_snd]
  set w : Spec (CommRingCat.of k) ⟶ pullback (pullback.snd f σ) (pullback.snd f σ) :=
    pullback.lift (pullback.lift (zbar ≫ pullback.fst f f) (𝟙 _) ha)
      (pullback.lift (zbar ≫ pullback.snd f f) (𝟙 _) hb) hab with hw_def
  have hwξ : w ≫ ξ = zbar := by
    apply pullback.hom_ext
    · rw [Category.assoc, hξfst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hξsnd, ← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have hwsnd : (w ≫ pullback.snd (pullback.snd f σ) (pullback.snd f σ)) ≫ pullback.fst f σ ≫ f = σ := by
    rw [pullback.lift_snd, ← Category.assoc, pullback.lift_fst, Category.assoc, pullback_snd_comp_eq_prodStr]
    exact hz

  calc zbar ≫ D.1 = w ≫ ξ ≫ D.1 := by rw [← Category.assoc, hwξ]
    _ = w ≫ φ ≫ pullback.fst g σ := by rw [hφB]
    _ = w ≫ (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫
          (pullback.lift (pullback.snd f σ ≫ x₀) (𝟙 (pullback f σ)) hm₂c ≫ φ)) ≫ pullback.fst g σ := by
        rw [← hfac]
    _ = (w ≫ pullback.snd (pullback.snd f σ) (pullback.snd f σ)) ≫
          (pullback.fst f σ ≫ f) ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        rw [Category.assoc, hχ]
        simp only [Category.assoc]
    _ = σ ≫ (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by rw [← Category.assoc, hwsnd]

theorem defect_apply_eq (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (z : ↥(pullback f f)) :
    (defect L M u hu (prodStr f f) (P₀ f) (Q₀ f)).1 z =
      (M.one (𝟙 (Spec (CommRingCat.of R)))).1 (prodStr f f z) := by
  let k : Type u := AlgebraicClosure ((pullback f f).residueField z)
  let zbar : Spec (CommRingCat.of k) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) k)) ≫
      (pullback f f).fromSpecResidueField z
  have hzbar : zbar (IsLocalRing.closedPoint k) = z := by
    show (Spec.map _ ≫ (pullback f f).fromSpecResidueField z) _ = z
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have h := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ B => φ (IsLocalRing.closedPoint k))
    (geomPoint_comp_defect hA L M u hu hone (zbar ≫ prodStr f f) zbar rfl)
  simp only [Scheme.Hom.comp_apply] at h
  rw [hzbar] at h
  exact h

theorem defect_universal_eq_one (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1) :
    defect L M u hu (prodStr f f) (P₀ f) (Q₀ f) = M.one (prodStr f f) := by
  set D : SchemeHomOver (prodStr f f) g := defect L M u hu (prodStr f f) (P₀ f) (Q₀ f) with hD_def

  set εX : Spec (CommRingCat.of R) ⟶ pullback f f :=
    (prodPairPt (L.one (𝟙 (Spec (CommRingCat.of R)))) (L.one (𝟙 (Spec (CommRingCat.of R))))).1 with hεX_def
  have hεX : εX ≫ prodStr f f = 𝟙 _ :=
    (prodPairPt (L.one (𝟙 (Spec (CommRingCat.of R)))) (L.one (𝟙 (Spec (CommRingCat.of R))))).2
  have hεXD : εX ≫ D.1 = (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    rw [hεX_def, hD_def, pair_comp_defect L M u hu, defect_one_left L M u hu hone]

  have hcollapse : ∀ z : ↥(pullback f f), D.1 (εX (prodStr f f z)) = D.1 z := by
    intro z
    rw [hD_def, defect_apply_eq hA L M u hu hone z, ← Scheme.Hom.comp_apply, ← hD_def, hεXD]

  have hrig := AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app (prodStr f f) εX hεX
    (isClosedMap_prodStr hA) (fun U _ => surjective_app_prodStr hA U) D.1 hcollapse
  rw [hεXD, ← one_coe M] at hrig
  exact Subtype.ext hrig.symm

theorem mul_comp_eq_mul_comp (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g) (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 ≫ u =
      (M.mul t ⟨P.1 ≫ u, by rw [Category.assoc, hu, P.2]⟩ ⟨Q.1 ≫ u, by rw [Category.assoc, hu, Q.2]⟩).1 := by
  have hD := defect_universal_eq_one hA L M u hu hone
  have h := defect_natural L M u hu (prodStr f f) t (prodPairPt P Q).1 (prodPairPt P Q).2 (P₀ f) (Q₀ f)
  rw [comp_P₀, comp_Q₀, hD, M.one_natural] at h
  exact congrArg Subtype.val (mul_of_defect_eq_one L M u hu t P Q h.symm)

end HomOfUnitBody
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one.HomOfUnitBody"

open HomOfUnitBody in
theorem solution
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g)
    (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 ≫ u =
      (M.mul t ⟨P.1 ≫ u, by rw [Category.assoc, hu, P.2]⟩ ⟨Q.1 ≫ u, by rw [Category.assoc, hu, Q.2]⟩).1 :=
  mul_comp_eq_mul_comp hA L M u hu hone t P Q

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one (solution)
