-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smoothProperCurves_sum_surjective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4871bbba-b72d-51af-b99d-4dc0e2464e83

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

noncomputable section

namespace K2

section GroupLaw

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.one t) * schemeHomOverComp ψ hψ (L.one t) = schemeHomOverComp ψ hψ (L.one t) := by
    show L.mul t' _ _ = _
    rw [← L.mul_natural, L.one_mul]
  exact mul_right_cancel (h.trans (one_mul _).symm)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural, L.inv_mul_cancel, one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem foldr_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (l : List (SchemeHomOver t f)) :
    schemeHomOverComp ψ hψ (l.foldr (fun Q R' => L.mul t Q R') (L.one t)) =
      (l.map (schemeHomOverComp ψ hψ)).foldr (fun Q R' => L.mul t' Q R') (L.one t') := by
  induction l with
  | nil => exact one_natural L t t' ψ hψ
  | cons x l ih => simp only [List.foldr_cons, List.map_cons, L.mul_natural, ih]

def univPt (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

theorem eq_comp_univPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) :
    x = schemeHomOverComp x.1 x.2 (univPt f) :=
  Subtype.ext (Category.comp_id _).symm

def invHom : A ⟶ A := (L.inv f (univPt f)).1

theorem invHom_comp : (invHom L) ≫ f = f := (L.inv f (univPt f)).2

theorem inv_eq_mapPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    L.inv t x = mapPt (invHom L) (invHom_comp L) x := by
  conv_lhs => rw [eq_comp_univPt x]
  rw [← inv_natural]
  rfl

def constPt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : SchemeHomOver f f :=
  schemeHomOverComp f (Category.comp_id f) a

def transHom (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (L.mul f (constPt a) (univPt f)).1

theorem transHom_comp (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : transHom L a ≫ f = f :=
  (L.mul f (constPt a) (univPt f)).2

theorem mul_const_eq_mapPt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    L.mul t (schemeHomOverComp t (Category.comp_id t) a) x = mapPt (transHom L a) (transHom_comp L a) x := by
  have h1 : schemeHomOverComp t (Category.comp_id t) a = schemeHomOverComp x.1 x.2 (constPt a) := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, constPt]
    rw [← Category.assoc, x.2]
  rw [h1]
  refine (congrArg (L.mul t _) (eq_comp_univPt x)).trans ?_
  rw [← L.mul_natural]
  rfl

end GroupLaw

section Main

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

structure CurveDatum where
  C : Scheme.{0}
  c : C ⟶ Spec (CommRingCat.of k)
  ν : C ⟶ A
  hν : ν ≫ f = c
  proper : IsProper c
  smooth : SmoothOfRelativeDimension 1 c
  integral : IsIntegral C

def foldPts {n : ℕ} (x : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
  (List.ofFn x).foldr (fun Q R' => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R') (L.one (𝟙 (Spec (CommRingCat.of k))))

structure Fam where
  curves : List (CurveDatum k f)
  P : Scheme.{0}
  p : P ⟶ Spec (CommRingCat.of k)
  proper : IsProper p
  irred : IrreducibleSpace ↥P
  σ : P ⟶ A
  hσ : σ ≫ f = p
  repr : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
    ∃ ys : ∀ i : Fin curves.length, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (curves[i]).c,
      mapPt σ hσ y = foldPts k f L (fun i => mapPt (curves[i]).ν (curves[i]).hν (ys i))
  one_mem : (L.one (𝟙 (Spec (CommRingCat.of k)))).1.base (IsLocalRing.closedPoint k) ∈ Set.range σ.base

def Fam.B (F : Fam k f L) : Set ↥A := Set.range F.σ.base

def fam₀ : Fam k f L where
  curves := []
  P := Spec (CommRingCat.of k)
  p := 𝟙 _
  proper := inferInstance
  irred := inferInstance
  σ := (L.one (𝟙 (Spec (CommRingCat.of k)))).1
  hσ := (L.one (𝟙 (Spec (CommRingCat.of k)))).2
  repr := fun y => ⟨fun i => Fin.elim0 (by simpa using i), by
    have hy : y.1 = 𝟙 _ := by simpa using y.2
    apply Subtype.ext
    simp only [mapPt_coe, hy, Category.id_comp, foldPts, List.ofFn_zero, List.foldr_nil]⟩
  one_mem := ⟨IsLocalRing.closedPoint k, rfl⟩

variable {k f L}

def dinv (L : RelativeGroupLaw k f) (D : CurveDatum k f) : CurveDatum k f :=
  ⟨D.C, D.c, D.ν ≫ invHom L, by rw [Category.assoc, invHom_comp, D.hν], D.proper, D.smooth, D.integral⟩

namespace Fam

variable (F : Fam k f L) (D : CurveDatum k f)

def Q : Scheme.{0} := pullback D.c F.p
def q : F.Q D ⟶ Spec (CommRingCat.of k) := pullback.fst D.c F.p ≫ D.c
def P' : Scheme.{0} := pullback D.c (F.q D)
def p' : F.P' D ⟶ Spec (CommRingCat.of k) := pullback.fst D.c (F.q D) ≫ D.c

theorem p'_eq : F.p' D = pullback.snd D.c (F.q D) ≫ F.q D := pullback.condition
theorem q_eq : F.q D = pullback.snd D.c F.p ≫ F.p := pullback.condition

def X₁ : SchemeHomOver (F.p' D) f := ⟨pullback.fst D.c (F.q D) ≫ D.ν, by rw [Category.assoc, D.hν]; rfl⟩
def X₂ : SchemeHomOver (F.p' D) f :=
  ⟨pullback.snd D.c (F.q D) ≫ pullback.fst D.c F.p ≫ D.ν ≫ invHom L, by
    simp only [Category.assoc, invHom_comp, D.hν]; rw [p'_eq]; rfl⟩
def X₃ : SchemeHomOver (F.p' D) f :=
  ⟨pullback.snd D.c (F.q D) ≫ pullback.snd D.c F.p ≫ F.σ, by
    simp only [Category.assoc, F.hσ]
    rw [p'_eq]
    exact congrArg (pullback.snd D.c (F.q D) ≫ ·) (F.q_eq D).symm⟩

def σ' : SchemeHomOver (F.p' D) f := L.mul (F.p' D) (F.X₁ D) (L.mul (F.p' D) (F.X₂ D) (F.X₃ D))

scoped instance : IsProper (F.q D) := by
  letI : IsProper F.p := F.proper
  letI : IsProper D.c := D.proper
  show IsProper (pullback.fst D.c F.p ≫ D.c)
  infer_instance

scoped instance : IsProper (F.p' D) := by
  letI : IsProper D.c := D.proper
  show IsProper (pullback.fst D.c (F.q D) ≫ D.c)
  infer_instance

scoped instance : IrreducibleSpace ↥(F.P' D) := by
  letI : IrreducibleSpace ↥F.P := F.irred
  letI : IsProper D.c := D.proper
  letI : IsIntegral D.C := D.integral
  haveI : GeometricallyIrreducible D.c := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed D.c
  haveI : UniversallyOpen D.c := inferInstance
  haveI : IrreducibleSpace ↥(F.Q D) := by unfold Q; infer_instance
  unfold P'
  infer_instance

end Fam
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam"

end Main
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam"

section Main2

variable {k : Type} [Field k] [IsAlgClosed k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
  {L : RelativeGroupLaw k f}

theorem exists_pt {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [Nonempty ↥X] :
    ∃ z : Spec (CommRingCat.of k) ⟶ X, z ≫ g = 𝟙 _ := by
  haveI : JacobsonSpace ↥X := jacobsonSpace_of_locallyOfFiniteType g
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set ↥X).Nonempty) isOpen_univ.isLocallyClosed
  obtain ⟨z, hz, -⟩ := Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton g k x hx
  refine ⟨z, ?_⟩
  rw [hz, Algebra.algebraMap_self, CommRingCat.ofHom_id]
  exact Spec.map_id _

namespace Fam

variable (F : Fam k f L) (D : CurveDatum k f)

theorem foldPts_succ {n : ℕ} (x : Fin (n + 1) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    foldPts k f L x = L.mul (𝟙 _) (x 0) (foldPts k f L (fun i => x i.succ)) := by
  simp only [foldPts, List.ofFn_succ, List.foldr_cons]

theorem repr' (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (F.p' D)) :
    ∃ ys : ∀ i : Fin (D :: dinv L D :: F.curves).length,
        SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) ((D :: dinv L D :: F.curves)[i]).c,
      mapPt (F.σ' D).1 (F.σ' D).2 y =
        foldPts k f L (fun i => mapPt ((D :: dinv L D :: F.curves)[i]).ν ((D :: dinv L D :: F.curves)[i]).hν (ys i)) := by
  have hy : y.1 ≫ F.p' D = 𝟙 _ := y.2

  let y₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c := ⟨y.1 ≫ pullback.fst D.c (F.q D), by
    rw [Category.assoc]; exact hy⟩
  let yQ : Spec (CommRingCat.of k) ⟶ F.Q D := y.1 ≫ pullback.snd D.c (F.q D)
  have hyQ : yQ ≫ F.q D = 𝟙 _ :=
    ((Category.assoc _ _ _).trans (congrArg (y.1 ≫ ·) (F.p'_eq D).symm)).trans hy
  let y₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c := ⟨yQ ≫ pullback.fst D.c F.p, by
    rw [Category.assoc]; exact hyQ⟩
  let y₃ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) F.p := ⟨yQ ≫ pullback.snd D.c F.p,
    ((Category.assoc _ _ _).trans (congrArg (yQ ≫ ·) (F.q_eq D).symm)).trans hyQ⟩
  obtain ⟨ys, hys⟩ := F.repr y₃
  refine ⟨Fin.cases y₁ (fun j => Fin.cases y₂ (fun j' => ys j') j), ?_⟩
  rw [foldPts_succ, foldPts_succ]

  have hL : mapPt (F.σ' D).1 (F.σ' D).2 y = schemeHomOverComp y.1 hy (F.σ' D) := Subtype.ext rfl
  rw [hL, σ', L.mul_natural, L.mul_natural]
  have e1 : schemeHomOverComp y.1 hy (F.X₁ D) = mapPt D.ν D.hν y₁ := Subtype.ext (by
    show y.1 ≫ (pullback.fst D.c (F.q D) ≫ D.ν) = (y.1 ≫ pullback.fst D.c (F.q D)) ≫ D.ν
    rw [Category.assoc])
  have e2 : schemeHomOverComp y.1 hy (F.X₂ D) = mapPt (dinv L D).ν (dinv L D).hν y₂ := Subtype.ext (by
    show y.1 ≫ (pullback.snd D.c (F.q D) ≫ pullback.fst D.c F.p ≫ D.ν ≫ invHom L) =
      ((y.1 ≫ pullback.snd D.c (F.q D)) ≫ pullback.fst D.c F.p) ≫ (D.ν ≫ invHom L)
    simp only [Category.assoc])
  have e3 : schemeHomOverComp y.1 hy (F.X₃ D) = mapPt F.σ F.hσ y₃ := Subtype.ext (by
    show y.1 ≫ (pullback.snd D.c (F.q D) ≫ pullback.snd D.c F.p ≫ F.σ) =
      ((y.1 ≫ pullback.snd D.c (F.q D)) ≫ pullback.snd D.c F.p) ≫ F.σ
    simp only [Category.assoc])
  rw [e1, e2, e3, hys]
  rfl

theorem trans_mem (y z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (ha : a = L.mul (𝟙 _) (mapPt D.ν D.hν y) (mapPt (dinv L D).ν (dinv L D).hν z))
    {b : ↥A} (hb : b ∈ Set.range F.σ.base) :
    (transHom L a).base b ∈ Set.range (F.σ' D).1.base := by
  subst ha
  obtain ⟨w, rfl⟩ := hb
  let s : Spec (F.P.residueField w) ⟶ Spec (CommRingCat.of k) := F.P.fromSpecResidueField w ≫ F.p
  obtain ⟨mQ, hmQ1, hmQ2⟩ : ∃ mQ : Spec (F.P.residueField w) ⟶ F.Q D,
      mQ ≫ pullback.fst D.c F.p = s ≫ z.1 ∧ mQ ≫ pullback.snd D.c F.p = F.P.fromSpecResidueField w :=
    ⟨pullback.lift (s ≫ z.1) (F.P.fromSpecResidueField w) (by rw [Category.assoc, z.2, Category.comp_id]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hmQ : mQ ≫ F.q D = s := by
    show mQ ≫ (pullback.fst D.c F.p ≫ D.c) = s
    rw [← Category.assoc, hmQ1, Category.assoc, z.2, Category.comp_id]
  obtain ⟨m, hm1, hm2⟩ : ∃ m : Spec (F.P.residueField w) ⟶ F.P' D,
      m ≫ pullback.fst D.c (F.q D) = s ≫ y.1 ∧ m ≫ pullback.snd D.c (F.q D) = mQ :=
    ⟨pullback.lift (s ≫ y.1) mQ (by rw [Category.assoc, y.2, Category.comp_id, hmQ]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hm : m ≫ F.p' D = s := by
    show m ≫ (pullback.fst D.c (F.q D) ≫ D.c) = s
    rw [← Category.assoc, hm1, Category.assoc, y.2, Category.comp_id]
  refine ⟨m.base (IsLocalRing.closedPoint _), ?_⟩
  rw [← Scheme.Hom.comp_apply]

  have key : m ≫ (F.σ' D).1 = (F.P.fromSpecResidueField w ≫ F.σ) ≫
      transHom L (L.mul (𝟙 _) (mapPt D.ν D.hν y) (mapPt (dinv L D).ν (dinv L D).hν z)) := by
    have h0 : m ≫ (F.σ' D).1 = (schemeHomOverComp m hm (F.σ' D)).1 := rfl
    rw [h0, σ', L.mul_natural, L.mul_natural]
    have e1 : schemeHomOverComp m hm (F.X₁ D) = schemeHomOverComp s (Category.comp_id s) (mapPt D.ν D.hν y) :=
      Subtype.ext (by
        show m ≫ (pullback.fst D.c (F.q D) ≫ D.ν) = s ≫ (y.1 ≫ D.ν)
        rw [← Category.assoc, hm1, Category.assoc])
    have e2 : schemeHomOverComp m hm (F.X₂ D) =
        schemeHomOverComp s (Category.comp_id s) (mapPt (dinv L D).ν (dinv L D).hν z) :=
      Subtype.ext (by
        show m ≫ (pullback.snd D.c (F.q D) ≫ pullback.fst D.c F.p ≫ D.ν ≫ invHom L) = s ≫ (z.1 ≫ (D.ν ≫ invHom L))
        rw [← Category.assoc, hm2, ← Category.assoc, hmQ1, Category.assoc])
    have e3 : schemeHomOverComp m hm (F.X₃ D) = ⟨F.P.fromSpecResidueField w ≫ F.σ, by
        rw [Category.assoc, F.hσ]⟩ := Subtype.ext (by
        show m ≫ (pullback.snd D.c (F.q D) ≫ pullback.snd D.c F.p ≫ F.σ) = F.P.fromSpecResidueField w ≫ F.σ
        rw [← Category.assoc, hm2, ← Category.assoc, hmQ2])
    rw [e1, e2, e3, ← L.mul_assoc, ← L.mul_natural, mul_const_eq_mapPt]
    rfl
  rw [key, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem mem_step {b : ↥A} (hb : b ∈ Set.range F.σ.base) : b ∈ Set.range (F.σ' D).1.base := by
  letI : IsIntegral D.C := D.integral
  letI : IsProper D.c := D.proper
  obtain ⟨y₀, hy₀⟩ := exists_pt D.c

  have hinv : mapPt (dinv L D).ν (dinv L D).hν ⟨y₀, hy₀⟩ = L.inv (𝟙 _) (mapPt D.ν D.hν ⟨y₀, hy₀⟩) := by
    rw [inv_eq_mapPt]; exact Subtype.ext (Category.assoc _ _ _).symm
  have hone : L.one (𝟙 _) = L.mul (𝟙 _) (mapPt D.ν D.hν ⟨y₀, hy₀⟩) (mapPt (dinv L D).ν (dinv L D).hν ⟨y₀, hy₀⟩) := by
    rw [hinv]; letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); exact (mul_inv_cancel _).symm
  have h := F.trans_mem D ⟨y₀, hy₀⟩ ⟨y₀, hy₀⟩ (L.one (𝟙 _)) hone hb
  have hτ : transHom L (L.one (𝟙 _)) = 𝟙 A := by
    have := mul_const_eq_mapPt L (L.one (𝟙 _)) f (univPt f)
    rw [one_natural, L.one_mul] at this
    exact (Category.id_comp _).symm.trans (congrArg Subtype.val this).symm
  rw [hτ] at h
  simpa using h

def step : Fam k f L where
  curves := D :: dinv L D :: F.curves
  P := F.P' D
  p := F.p' D
  proper := inferInstance
  irred := inferInstance
  σ := (F.σ' D).1
  hσ := (F.σ' D).2
  repr := F.repr' D
  one_mem := F.mem_step D F.one_mem

theorem B_subset_step : F.B ⊆ (F.step D).B := fun _ hb => F.mem_step D hb

theorem step_B : (F.step D).B = Set.range (F.σ' D).1.base := rfl

end Fam
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam"

end Main2
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam"

section Final

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f) (g : ℕ)
  (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)

include hA in
theorem isIntegral_A : IsIntegral A := by
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : ConnectedSpace ↥A := by
    rw [connectedSpace_iff_univ]
    obtain ⟨S, hS, hS'⟩ : ∃ S : Set ↥A, _root_.IsConnected S ∧ S = Set.univ :=
      ⟨_, hA.connectedFibres (IsLocalRing.closedPoint k), Set.eq_univ_of_forall fun x => Subsingleton.elim _ _⟩
    subst hS'
    exact hS
  haveI : GeometricallyConnected f := geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace k f
  haveI : GeometricallyIntegral f := geometricallyIntegral_of_smooth_of_geometricallyConnected f
  haveI : UniversallyOpen f := inferInstance
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Flat f := inferInstance
  exact GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen f

variable {k f L}

theorem Fam.isClosed_B (hA : AbelianSchemePropertyBundle k f) (F : Fam k f L) : IsClosed F.B := by
  haveI : IsProper f := hA.proper
  haveI : IsProper (F.σ ≫ f) := by rw [F.hσ]; exact F.proper
  haveI : IsProper F.σ := IsProper.of_comp F.σ f
  exact F.σ.isClosedMap.isClosed_range

theorem Fam.isIrreducible_B (F : Fam k f L) : IsIrreducible F.B := by
  letI := F.irred
  rw [Fam.B, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ ↥F.P).image F.σ.base F.σ.base.hom.continuous.continuousOn

include hdim in
theorem dim_A : topologicalKrullDim ↥A = g := by
  obtain ⟨S, hS, hS'⟩ : ∃ S : Set ↥A, topologicalKrullDim ↥S = g ∧ S = Set.univ :=
    ⟨_, hdim (IsLocalRing.closedPoint k), Set.eq_univ_of_forall fun x => Subsingleton.elim _ _⟩
  subst hS'
  rw [← hS]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ ↥A).isHomeomorph).symm

include hdim in
theorem Fam.dim_B_le (F : Fam k f L) : topologicalKrullDim ↥F.B ≤ g :=
  (topologicalKrullDim_subspace_le _ _).trans (dim_A (f := f) g hdim).le

theorem transHom_apply_eq (D : CurveDatum k f) (p q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c) :
    (transHom L (L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p))).base
      ((mapPt D.ν D.hν p).1.base (IsLocalRing.closedPoint k)) =
      (mapPt D.ν D.hν q).1.base (IsLocalRing.closedPoint k) := by
  rw [← Scheme.Hom.comp_apply]
  have hinv : mapPt (dinv L D).ν (dinv L D).hν p = L.inv (𝟙 _) (mapPt D.ν D.hν p) := by
    rw [inv_eq_mapPt]; exact Subtype.ext (Category.assoc _ _ _).symm
  have key : (mapPt D.ν D.hν p).1 ≫ transHom L (L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p)) =
      (mapPt D.ν D.hν q).1 := by
    have h := mul_const_eq_mapPt L (L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p)) (𝟙 _)
      (mapPt D.ν D.hν p)
    have h1 : schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _)
        (L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p)) =
        L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p) := Subtype.ext (Category.id_comp _)
    letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
    have h2 : (mapPt D.ν D.hν q) * (mapPt D.ν D.hν p)⁻¹ * (mapPt D.ν D.hν p) = mapPt D.ν D.hν q := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have h3 : L.mul (𝟙 _) (L.mul (𝟙 _) (mapPt D.ν D.hν q) (mapPt (dinv L D).ν (dinv L D).hν p)) (mapPt D.ν D.hν p) =
        mapPt D.ν D.hν q := by rw [hinv]; exact h2
    rw [h1, h3] at h
    exact (congrArg Subtype.val h).symm
  rw [key]

theorem Fam.exists_step_ne (hA : AbelianSchemePropertyBundle k f) (F : Fam k f L) (hne : F.B ≠ Set.univ) :
    ∃ F' : Fam k f L, F.B ⊆ F'.B ∧ F.B ≠ F'.B := by
  classical
  haveI : IsProper f := hA.proper
  haveI : IsIntegral A := isIntegral_A k f hA

  obtain ⟨x, hxB, s₁, hs₁, hs₁x⟩ : ∃ x, x ∉ F.B ∧ ∃ s : Spec (CommRingCat.of k) ⟶ A, s ≫ f = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint k) = x := by
    have hopen : IsOpen F.Bᶜ := (F.isClosed_B hA).isOpen_compl
    have hne' : (F.Bᶜ).Nonempty := Set.nonempty_compl.mpr hne
    obtain ⟨x, hx, hx'⟩ := (dense_setOf_exists_section_of_isAlgClosed f).inter_open_nonempty _ hopen hne'
    exact ⟨x, hx, hx'⟩
  by_contra H
  push Not at H
  apply hxB
  rw [← hs₁x]

  refine mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem f
    {P : Spec (CommRingCat.of k) ⟶ A | P.base (IsLocalRing.closedPoint k) ∈ F.B}
    (L.one (𝟙 _)).1 (L.one (𝟙 _)).2 F.one_mem ?_ s₁ hs₁
  intro C c _ _ _ U ψ hψ p q hp hq hpS

  have hU : (U : Set ↥C).Nonempty := ⟨(p.base (IsLocalRing.closedPoint k)).1, (p.base (IsLocalRing.closedPoint k)).2⟩
  obtain ⟨ν, hν, hUν⟩ := exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper c f U hU ψ hψ
  let D : CurveDatum k f := ⟨C, c, ν, hν, ‹_›, ‹_›, ‹_›⟩
  let pb : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c := ⟨p ≫ U.ι, by rw [Category.assoc]; exact hp⟩
  let qb : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.c := ⟨q ≫ U.ι, by rw [Category.assoc]; exact hq⟩
  have hpν : (mapPt D.ν D.hν pb).1 = p ≫ ψ := by
    show (p ≫ U.ι) ≫ ν = p ≫ ψ
    rw [Category.assoc, hUν]
  have hqν : (mapPt D.ν D.hν qb).1 = q ≫ ψ := by
    show (q ≫ U.ι) ≫ ν = q ≫ ψ
    rw [Category.assoc, hUν]
  have hpB : (mapPt D.ν D.hν pb).1.base (IsLocalRing.closedPoint k) ∈ F.B := by rw [hpν]; exact hpS

  have hEq := H (F.step D) (F.B_subset_step D)
  have hq' : (mapPt D.ν D.hν qb).1.base (IsLocalRing.closedPoint k) ∈ (F.step D).B := by
    rw [← transHom_apply_eq D pb qb]
    exact F.trans_mem D qb pb _ rfl hpB
  show (q ≫ ψ).base (IsLocalRing.closedPoint k) ∈ F.B
  rw [← hqν, hEq]
  exact hq'

theorem exists_fam_dim (hA : AbelianSchemePropertyBundle k f) :
    ∀ m : ℕ, ∃ F : Fam k f L, F.B = Set.univ ∨ (m : WithBot ℕ∞) ≤ topologicalKrullDim ↥F.B := by
  intro m
  induction m with
  | zero =>
    refine ⟨fam₀ k f L, Or.inr ?_⟩
    obtain ⟨b, hb⟩ : (fam₀ k f L).B.Nonempty := ⟨_, (fam₀ k f L).one_mem⟩
    haveI : Nonempty (TopologicalSpace.IrreducibleCloseds ↥(fam₀ k f L).B) :=
      ⟨⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  | succ m ih =>
    obtain ⟨F, hF | hF⟩ := ih
    · exact ⟨F, Or.inl hF⟩
    by_cases hB : F.B = Set.univ
    · exact ⟨F, Or.inl hB⟩
    obtain ⟨F', hsub, hne⟩ := F.exists_step_ne hA hB
    refine ⟨F', Or.inr ?_⟩
    have h := F'.isIrreducible_B.topologicalKrullDim_add_one_le_of_isClosed_of_ne (F.isClosed_B hA) hsub hne
    calc ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) + 1 := by push_cast; rfl
      _ ≤ topologicalKrullDim ↥F.B + 1 := add_le_add hF le_rfl
      _ ≤ topologicalKrullDim ↥F'.B := h

include hdim in
theorem exists_fam_univ (hA : AbelianSchemePropertyBundle k f) : ∃ F : Fam k f L, F.B = Set.univ := by
  obtain ⟨F, hF | hF⟩ := exists_fam_dim hA (g + 1)
  · exact ⟨F, hF⟩
  have h := hF.trans (F.dim_B_le g hdim)
  exfalso
  have : ((g + 1 : ℕ) : WithBot ℕ∞) ≤ (g : ℕ) := h
  norm_cast at this
  omega

end Final
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam"

theorem main
    (k : Type) [Field k] [IsAlgClosed k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f) (g : ℕ)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) :
    ∃ (n : ℕ) (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
      (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i),
      (∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i)) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
              (L.one (𝟙 (Spec (CommRingCat.of k)))) = P := by
  haveI : IsProper f := hA.proper
  obtain ⟨F, hF⟩ := exists_fam_univ (L := L) g hdim hA
  haveI : IsProper F.p := F.proper
  haveI : IsProper (F.σ ≫ f) := by rw [F.hσ]; exact F.proper
  haveI : IsProper F.σ := IsProper.of_comp F.σ f
  refine ⟨F.curves.length, fun i => (F.curves[i]).C, fun i => (F.curves[i]).c, fun i => (F.curves[i]).ν,
    fun i => (F.curves[i]).hν, fun i => ⟨(F.curves[i]).proper, (F.curves[i]).smooth, (F.curves[i]).integral⟩,
    fun P => ?_⟩

  obtain ⟨w, hw⟩ : P.1.base (IsLocalRing.closedPoint k) ∈ F.B := hF.symm ▸ Set.mem_univ _
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := P.1) (g := F.σ) (IsLocalRing.closedPoint k) w hw.symm
  haveI : Nonempty ↥(pullback P.1 F.σ) := ⟨z₀⟩
  obtain ⟨zT, hzT⟩ := exists_pt (pullback.fst P.1 F.σ)
  let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) F.p := ⟨zT ≫ pullback.snd P.1 F.σ, by
    rw [Category.assoc, ← F.hσ, ← Category.assoc (pullback.snd P.1 F.σ), ← pullback.condition, Category.assoc, P.2,
      Category.comp_id]
    exact hzT⟩
  obtain ⟨ys, hys⟩ := F.repr y
  refine ⟨ys, ?_⟩
  have hyP : mapPt F.σ F.hσ y = P := Subtype.ext (by
    show (zT ≫ pullback.snd P.1 F.σ) ≫ F.σ = P.1
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hzT, Category.id_comp])
  rw [← hyP, hys]
  rfl

end K2
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2.Fam P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.K2"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f) (g : ℕ)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) :
    ∃ (n : ℕ) (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
      (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i),
      (∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i)) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
              (L.one (𝟙 (Spec (CommRingCat.of k)))) = P :=
  K2.main k f L hA g hdim

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed (solution)
