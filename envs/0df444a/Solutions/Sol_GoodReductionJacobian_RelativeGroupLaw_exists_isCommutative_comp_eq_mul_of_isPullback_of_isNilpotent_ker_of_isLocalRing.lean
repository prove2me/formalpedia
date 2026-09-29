-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/19c131aa-2f40-5e84-9b3b-0fbd88074c31

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_smallExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

namespace E3Body

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {S : Scheme.{u}} {t t' : S ⟶ Spec (CommRingCat.of R)} (h : t = t') (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

set_option maxHeartbeats 6400000 in

theorem aux (k : ℕ) : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle T f₀) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f) (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (hJ : RingHom.ker π * maximalIdeal T' ^ k = ⊥),
    ∃ (L : RelativeGroupLaw T' f) (_ : L.IsCommutative) (_ : AbelianSchemePropertyBundle T' f),
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t f₀),
        (L₀.mul t P Q).1 ≫ g =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 := by
  induction k with
  | zero =>
    intro T' T _ _ _ _ π hπ hker A₀ f₀ L₀ hc₀ h₀ A f hs hp g hg hJ
    rw [pow_zero, Ideal.one_eq_top, Ideal.mul_top] at hJ
    exact GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension T' T π hπ hker
      (by rw [hJ, Ideal.bot_mul]) f₀ L₀ hc₀ h₀ f hs hp g hg
  | succ k ih =>
    intro T' T _ _ _ _ π hπ hker A₀ f₀ L₀ hc₀ h₀ A f hs hp g hg hJ

    have hkertop : RingHom.ker π ≠ ⊤ := by
      intro htop
      obtain ⟨n, hn⟩ := hker
      rw [htop, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top] at hn
      exact (top_ne_bot hn)
    have hJle : RingHom.ker π * maximalIdeal T' ^ k ≤ RingHom.ker π := Ideal.mul_le_left
    have hJm : RingHom.ker π * maximalIdeal T' ^ k ≤ maximalIdeal T' := hJle.trans (IsLocalRing.le_maximalIdeal hkertop)
    haveI hnt : Nontrivial (T' ⧸ (RingHom.ker π * maximalIdeal T' ^ k)) :=
      Ideal.Quotient.nontrivial_iff.mpr (fun h => (maximalIdeal.isMaximal T').ne_top (top_le_iff.mp (h ▸ hJm)))
    haveI hloc : IsLocalRing (T' ⧸ (RingHom.ker π * maximalIdeal T' ^ k)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

    have hπJ : ∀ a ∈ RingHom.ker π * maximalIdeal T' ^ k, π a = 0 := fun a ha => hJle ha
    have hfac : (Ideal.Quotient.lift _ π hπJ).comp (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k)) = π :=
      RingHom.ext fun _ => rfl
    have hπ'' : Function.Surjective (Ideal.Quotient.lift _ π hπJ) := by
      intro x; obtain ⟨a, rfl⟩ := hπ x; exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have hkermap : RingHom.ker (Ideal.Quotient.lift _ π hπJ) = (RingHom.ker π).map (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k)) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact Ideal.mem_map_of_mem _ hx
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        exact ha
    have hker'' : IsNilpotent (RingHom.ker (Ideal.Quotient.lift _ π hπJ)) := by
      obtain ⟨n, hn⟩ := hker
      exact ⟨n, by rw [hkermap, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
    have hJ'' : RingHom.ker (Ideal.Quotient.lift _ π hπJ) * maximalIdeal (T' ⧸ (RingHom.ker π * maximalIdeal T' ^ k)) ^ k = ⊥ := by
      rw [hkermap, ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
        ← Ideal.map_mul, Ideal.map_quotient_self]

    have hSpecπ : Spec.map (CommRingCat.ofHom π) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ π hπJ)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]
    haveI : Smooth (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))))) :=
      MorphismProperty.pullback_snd _ _ hs
    haveI : IsProper (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))))) :=
      MorphismProperty.pullback_snd _ _ hp
    have hw : g ≫ f = (f₀ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ π hπJ))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))) := by
      rw [hg.w, hSpecπ, Category.assoc]
    have hg' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))))
    have hlift₁ := Limits.pullback.lift_fst g _ hw
    have hlift₂ := Limits.pullback.lift_snd g _ hw
    have hg'' : IsPullback (Limits.pullback.lift g _ hw) f₀
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k)))))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ π hπJ))) := by
      refine IsPullback.of_right ?_ hlift₂ hg'
      rw [hlift₁, ← hSpecπ]
      exact hg

    have hIH := ih (T' ⧸ (RingHom.ker π * maximalIdeal T' ^ k)) T (Ideal.Quotient.lift _ π hπJ) hπ'' hker'' f₀ L₀ hc₀ h₀
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))))) inferInstance inferInstance
      (Limits.pullback.lift g _ hw) hg'' hJ''
    obtain ⟨L'', hc'', hA'', hom''⟩ := hIH
    have hkerq : IsNilpotent (RingHom.ker (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))) := by
      rw [Ideal.mk_ker]
      obtain ⟨n, hn⟩ := hker
      exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hJle n).trans hn.le)⟩
    have hsmallq : RingHom.ker (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k)) * maximalIdeal T' = ⊥ := by
      rw [Ideal.mk_ker, mul_assoc, ← pow_succ, hJ]
    have hGLL := GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension T' (T' ⧸ (RingHom.ker π * maximalIdeal T' ^ k))
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective hkerq hsmallq
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker π * maximalIdeal T' ^ k))))) L'' hc'' hA''
      f hs hp (Limits.pullback.fst f _) hg'
    obtain ⟨L, hc, hA, hom'⟩ := hGLL
    refine ⟨L, hc, hA, ?_⟩
    intro S t P Q
    have e1 := hom'' t P Q
    have e2 := hom' (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ π hπJ)))
      ⟨P.1 ≫ Limits.pullback.lift g _ hw, by rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ Limits.pullback.lift g _ hw, by rw [Category.assoc, hg''.w, ← Category.assoc, Q.2]⟩
    calc (L₀.mul t P Q).1 ≫ g
        = ((L₀.mul t P Q).1 ≫ Limits.pullback.lift g _ hw) ≫ Limits.pullback.fst f _ := by rw [Category.assoc, hlift₁]
      _ = _ := by rw [e1]
      _ = _ := e2
      _ = _ := mul_val_congr L (by rw [Category.assoc, ← hSpecπ]) _ _ _ _
            (by show (P.1 ≫ _) ≫ _ = P.1 ≫ g; rw [Category.assoc, hlift₁])
            (by show (Q.1 ≫ _) ≫ _ = Q.1 ≫ g; rw [Category.assoc, hlift₁])

end E3Body

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    ∃ (L : RelativeGroupLaw T' f) (_ : L.IsCommutative) (_ : AbelianSchemePropertyBundle T' f),
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t f₀),
        (L₀.mul t P Q).1 ≫ g =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, maximalIdeal T' ^ k = ⊥ := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T')
    exact ⟨k, by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hk⟩
  exact E3Body.aux k T' T π hπ hker f₀ L₀ hc₀ h₀ f hs hp g hg (by rw [hk, Ideal.mul_bot])

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing (solution)
