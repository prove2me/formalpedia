-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b3f3b8ab-416f-52cf-b439-fa8f0bb21706

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mH0UnivAbelianScheme

theorem bijective_of_forall_isPushout {T B : Type u} [CommRing T] [CommRing B] (φ : T →+* B)
    (Bp : ∀ (P : Ideal T) [P.IsMaximal], Type u) [∀ (P : Ideal T) [P.IsMaximal], CommRing (Bp P)]
    (ψ : ∀ (P : Ideal T) [P.IsMaximal], Localization.AtPrime P →+* Bp P)
    (χ : ∀ (P : Ideal T) [P.IsMaximal], B →+* Bp P)
    (hpush : ∀ (P : Ideal T) [P.IsMaximal],
      IsPushout (CommRingCat.ofHom (algebraMap T (Localization.AtPrime P))) (CommRingCat.ofHom φ)
        (CommRingCat.ofHom (ψ P)) (CommRingCat.ofHom (χ P)))
    (hψ : ∀ (P : Ideal T) [P.IsMaximal], Function.Bijective (ψ P)) :
    Function.Bijective φ := by
  letI : Algebra T B := φ.toAlgebra
  letI iBB : ∀ (P : Ideal T) [P.IsMaximal], Algebra B (Bp P) := fun P _ => (χ P).toAlgebra
  letI iLB : ∀ (P : Ideal T) [P.IsMaximal], Algebra (Localization.AtPrime P) (Bp P) :=
    fun P _ => (ψ P).toAlgebra
  letI iTB : ∀ (P : Ideal T) [P.IsMaximal], Algebra T (Bp P) := fun P _ => ((χ P).comp φ).toAlgebra
  haveI ist1 : ∀ (P : Ideal T) [P.IsMaximal], IsScalarTower T B (Bp P) :=
    fun P _ => IsScalarTower.of_algebraMap_eq' rfl
  haveI ist2 : ∀ (P : Ideal T) [P.IsMaximal], IsScalarTower T (Localization.AtPrime P) (Bp P) :=
    fun P _ => IsScalarTower.of_algebraMap_eq' (by
      have h := congrArg CommRingCat.Hom.hom (hpush P).w
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h

      exact h.symm)
  have hAP : ∀ (P : Ideal T) [P.IsMaximal],
      Algebra.IsPushout T (Localization.AtPrime P) B (Bp P) := fun P _ =>
    CommRingCat.isPushout_iff_isPushout.mp (hpush P)
  let g : ∀ (P : Ideal T) [P.IsMaximal], B →ₗ[T] Bp P :=
    fun P _ => (IsScalarTower.toAlgHom T B (Bp P)).toLinearMap
  haveI hg : ∀ (P : Ideal T) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) (g P)).mpr (hAP P).out
  refine bijective_of_isLocalized_maximal (R := T) (M := T) (N := B)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap T (Localization.AtPrime P))
    (fun P _ => Bp P) g (Algebra.linearMap T B) ?_
  intro P _
  have hmap : IsLocalizedModule.map P.primeCompl (Algebra.linearMap T (Localization.AtPrime P)) (g P)
        (Algebra.linearMap T B) =
      (Algebra.linearMap (Localization.AtPrime P) (Bp P)).restrictScalars T := by
    apply IsLocalizedModule.linearMap_ext (S := P.primeCompl)
      (f := Algebra.linearMap T (Localization.AtPrime P)) (f' := g P)
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext
    intro t
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.coe_restrictScalars, g, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [hmap]
  exact hψ P

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f :=
  ⟨fun K _ y Z fst snd h => by
    haveI : IrreducibleSpace ↥Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
    infer_instance⟩

theorem bijective_appTop_of_isLocalRing {T : Type u} [CommRing T] [IsLocalRing T] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of T)} (hp : AbelianSchemePropertyBundle T p) :
    Function.Bijective p.appTop := by
  haveI := hp.proper
  haveI := hp.smooth
  letI : Field (T ⧸ IsLocalRing.maximalIdeal T) := Ideal.Quotient.field _
  let ι : Spec (.of (T ⧸ IsLocalRing.maximalIdeal T)) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T)))
  have hk : AbelianSchemePropertyBundle (T ⧸ IsLocalRing.maximalIdeal T) (pullback.snd p ι) :=
    hp.of_isPullback (IsPullback.of_hasPullback p ι)
  haveI : GeometricallyIntegral (pullback.snd p ι) := hk.geometricallyIntegral
  haveI : GeometricallyConnected (pullback.snd p ι) :=
    geometricallyConnected_of_geometricallyIrreducible _
  have hfib :=
    bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
      (K := T ⧸ IsLocalRing.maximalIdeal T) (pullback.snd p ι)
  exact bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
    (A := .of T) p hfib

theorem bijective_appTop_of_abelianSchemePropertyBundle {T : Type u} [CommRing T] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of T)} (hp : AbelianSchemePropertyBundle T p) :
    Function.Bijective p.appTop := by
  haveI := hp.proper
  haveI := hp.smooth
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated p
  let φ : T →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of T)).inv ≫ p.appTop).hom
  suffices hφ : Function.Bijective φ by
    have hiso : Function.Bijective (Scheme.ΓSpecIso (.of T)).hom.hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of T)).hom
    have : p.appTop = (Scheme.ΓSpecIso (.of T)).hom ≫ ((Scheme.ΓSpecIso (.of T)).inv ≫ p.appTop) := by
      simp
    rw [this]
    exact hφ.comp hiso
  refine bijective_of_forall_isPushout φ
    (fun P _ => Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.AtPrime P)))), ⊤))
    (fun P _ => ((Scheme.ΓSpecIso (.of (Localization.AtPrime P))).inv ≫
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.AtPrime P))))).appTop).hom)
    (fun P _ => (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.AtPrime P))))).appTop.hom)
    (fun P _ => ?_) (fun P _ => ?_)
  · have h := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat (k := T) p (Localization.AtPrime P)
    exact h
  · have hP : AbelianSchemePropertyBundle (Localization.AtPrime P)
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.AtPrime P))))) :=
      hp.of_isPullback (IsPullback.of_hasPullback _ _)
    have h1 := bijective_appTop_of_isLocalRing hP
    have h2 : Function.Bijective (Scheme.ΓSpecIso (.of (Localization.AtPrime P))).inv.hom :=
      ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Localization.AtPrime P))).inv
    exact h1.comp h2

theorem appLE_top_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  (Scheme.Hom.app_eq_appLE f).symm

end P2mH0UnivAbelianScheme

open P2mH0UnivAbelianScheme in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (T : Type u) [CommRing T] [Algebra R T] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
    Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)) := by
  have hb : AbelianSchemePropertyBundle T (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) :=
    hA.of_isPullback (IsPullback.of_hasPullback _ _)
  have h := bijective_appTop_of_abelianSchemePropertyBundle hb
  have hiso : Function.Bijective (Scheme.ΓSpecIso (.of T)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of T)).inv
  show Function.Bijective ((Scheme.ΓSpecIso (.of T)).inv ≫
    (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)).appLE ⊤ ⊤ le_top).hom
  rw [appLE_top_top_eq_appTop]
  exact h.comp hiso

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback (solution)
