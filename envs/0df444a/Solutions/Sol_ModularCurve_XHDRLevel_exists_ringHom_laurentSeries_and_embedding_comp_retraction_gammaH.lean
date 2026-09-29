-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/66e1e817-3525-58af-9039-9db528ca0eb3

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_jqModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

noncomputable section

namespace RetrMinH

variable {p : ℕ} [Fact p.Prime]

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : R p →+* P) : f = g := by
  haveI : IsLocalization.AtPrime (R p) (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def tensorAddHom {A M L : Type*} [CommRing A] [Algebra (R p) A] [CommRing M] [Algebra (R p) M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[R p] M →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => F x * G b) (fun b b' => by simp only [map_add, mul_add]))
      (fun x x' => by ext b; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun r x b => by
      have key := RingHom.congr_fun (ringHom_ext_zp (p := p) (F.comp (algebraMap (R p) A)) (G.comp (algebraMap (R p) M))) r
      simp only [RingHom.coe_comp, Function.comp_apply] at key
      show F (r • x) * G b = F x * G (r • b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, key]
      ring)

theorem tensorAddHom_tmul {A M L : Type*} [CommRing A] [Algebra (R p) A] [CommRing M] [Algebra (R p) M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorAddHom (p := p) F G (x ⊗ₜ[R p] b) = F x * G b := by
  unfold tensorAddHom
  rw [TensorProduct.liftAddHom_tmul]
  rfl

def tensorRingHom {A M L : Type*} [CommRing A] [Algebra (R p) A] [CommRing M] [Algebra (R p) M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[R p] M →+* L :=
  { tensorAddHom (p := p) F G with
    map_one' := by
      show tensorAddHom (p := p) F G 1 = 1
      rw [Algebra.TensorProduct.one_def, tensorAddHom_tmul, map_one, map_one, one_mul]
    map_mul' := fun s t => by
      show tensorAddHom (p := p) F G (s * t) = tensorAddHom (p := p) F G s * tensorAddHom (p := p) F G t
      induction s using TensorProduct.induction_on with
      | zero => rw [zero_mul, map_zero, zero_mul]
      | tmul x b =>
        induction t using TensorProduct.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | tmul x' b' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, tensorAddHom_tmul, tensorAddHom_tmul, tensorAddHom_tmul, map_mul,
            map_mul]
          ring
        | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      | add s₁ s₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂] }

theorem tensorRingHom_tmul {A M L : Type*} [CommRing A] [Algebra (R p) A] [CommRing M] [Algebra (R p) M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorRingHom (p := p) F G (x ⊗ₜ[R p] b) = F x * G b :=
  tensorAddHom_tmul (p := p) F G x b

theorem isIntegral_of_mem (F : Type) [Field F] [Algebra (R p) F] (j : F) [Fact (j ≠ 0)]
    (κ : Type) [Field κ] [Algebra (R p) κ]
    (K : Subalgebra κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)))
    (hK : (1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j ∈ K)
    (z : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) :
    IsIntegral K z := by
  induction z using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | add x y hx hy => exact hx.add hy
  | tmul x b =>
    have hxb : x ⊗ₜ[R p] b = algebraMap κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) x * ((1 : κ) ⊗ₜ[R p] b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hxb]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_algebraMap (R := K) (x := ⟨_, K.algebraMap_mem x⟩)
    · obtain ⟨P, hPm, hP⟩ := (TwoChartIntegralModel.mem_chartAlg_iff (R p) F).mp b.2
      let incl : ↥(Algebra.adjoin (R p) ({j} : Set F)) →ₐ[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) :=
        Subalgebra.inclusion (TwoChartIntegralModel.adjoin_le_chartAlg (R p) F {j})
      let ρₐ : ↥(Algebra.adjoin (R p) ({j} : Set F)) →ₐ[R p] κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) :=
        (Algebra.TensorProduct.includeRight :
          ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) →ₐ[R p] κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)).comp incl
      have hρK : ∀ a : ↥(Algebra.adjoin (R p) ({j} : Set F)), ρₐ a ∈ K := by
        rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          have : ρₐ ⟨y, Algebra.subset_adjoin rfl⟩ = (1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F y := rfl
          rw [this]
          exact hK
        | algebraMap r =>
          have : (⟨algebraMap (R p) F r, Subalgebra.algebraMap_mem _ r⟩ : ↥(Algebra.adjoin (R p) ({j} : Set F))) =
              algebraMap (R p) _ r := rfl
          rw [this, AlgHom.commutes, IsScalarTower.algebraMap_apply (R p) κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))]
          exact K.algebraMap_mem _
        | add y y' hy hy' h h' =>
          have : (⟨y + y', add_mem hy hy'⟩ : ↥(Algebra.adjoin (R p) ({j} : Set F))) = ⟨y, hy⟩ + ⟨y', hy'⟩ := rfl
          rw [this, map_add]
          exact K.add_mem h h'
        | mul y y' hy hy' h h' =>
          have : (⟨y * y', mul_mem hy hy'⟩ : ↥(Algebra.adjoin (R p) ({j} : Set F))) = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
          rw [this, map_mul]
          exact K.mul_mem h h'
      have hroot : (P.map ρₐ.toRingHom).eval ((1 : κ) ⊗ₜ[R p] b) = 0 := by
        have h1 : P.eval₂ incl.toRingHom b = 0 := by
          apply Subtype.val_injective
          have := Polynomial.hom_eval₂ P incl.toRingHom (TwoChartIntegralModel.chartAlgFin (R p) F j).val.toRingHom b
          have hcomp : (TwoChartIntegralModel.chartAlgFin (R p) F j).val.toRingHom.comp incl.toRingHom =
              algebraMap ↥(Algebra.adjoin (R p) ({j} : Set F)) F :=
            RingHom.ext fun _ => rfl
          rw [hcomp] at this
          exact this.trans hP
        have h2 := Polynomial.hom_eval₂ P incl.toRingHom
          (Algebra.TensorProduct.includeRight :
            ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) →ₐ[R p] κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)).toRingHom b
        rw [h1, map_zero] at h2
        rw [Polynomial.eval_map]
        exact h2.symm
      have hlifts : P.map ρₐ.toRingHom ∈ Polynomial.lifts (algebraMap K (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map, Subalgebra.setRange_algebraMap]
        exact hρK _
      obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPm.map _)
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQmap]
      exact hroot

theorem coeffMap_jqModC {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') :
    coeffMap f (jqModC K) = jqModC K' := by
  ext k
  rw [coeffMap_coeff, ← map_jqModC f, HahnSeries.map_coeff]

theorem order_pow' {K : Type*} [Field K] (x : LaurentSeries K) (hx : x ≠ 0) (n : ℕ) : (x ^ n).order = n * x.order := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem eval₂_C_ne_zero {K : Type*} [Field K] (y : LaurentSeries K) (hy : y.order < 0)
    (P : Polynomial K) (hP : P ≠ 0) : P.eval₂ HahnSeries.C y ≠ 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [HahnSeries.order_zero] at hy
    exact lt_irrefl _ hy
  set n := P.natDegree with hn
  have hlead : P.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  intro h
  have hc := congrArg (fun s : LaurentSeries K => s.coeff (n * y.order)) h
  simp only [HahnSeries.coeff_zero] at hc
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at hc
  · refine mul_ne_zero hlead ?_ hc
    rw [← order_pow' y hy0 n]
    exact (mt HahnSeries.coeff_order_eq_zero.mp (pow_ne_zero n hy0))
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
    rw [order_pow' y hy0 i]
    have : (i : ℤ) < n := by exact_mod_cast hi
    nlinarith

theorem false_of_one_tmul_j_eq_pow {O : Type*} [CommRing O] [Algebra (R p) O] (jN : O)
    (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    (g₀ : O →+* LaurentSeries κ) (hg₀ : g₀ jN = jqModC κ)
    (s : κ ⊗[R p] O) (hs : (1 : κ) ⊗ₜ[R p] jN = s ^ p) : False := by
  let χ : κ ⊗[R p] O →+* LaurentSeries κ := tensorRingHom (p := p) HahnSeries.C g₀
  have hχj : χ ((1 : κ) ⊗ₜ[R p] jN) = jqModC κ := by
    show tensorRingHom (p := p) _ _ _ = _
    rw [tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC κ := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    exact jqModC_ne_zero κ hpow.symm
  have h := congrArg HahnSeries.order hpow
  rw [order_pow' x hx0, order_jqModC] at h
  have hdvd : (p : ℤ) ∣ 1 := ⟨-x.order, by linarith⟩
  have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem one_tmul_natCast_mul (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    {O : Type*} [CommRing O] [Algebra (R p) O] (c : O) :
    (1 : κ) ⊗ₜ[R p] (((p : ℕ) : O) * c) = 0 := by
  rw [show ((p : ℕ) : O) * c = ((p : ℕ) : R p) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem isDomain_tensor_chartAlgFin_gammaN
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    [Nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))] :
    IsDomain (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM :=
    ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) :=
    CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)
  haveI hint := ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
    (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hpN (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj) κ
  obtain ⟨g, hg, -, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin
    (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) κ
  haveI := hg
  let e : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ :=
    Algebra.TensorProduct.comm (R p) κ ↥(chartAlgFin p (ΓN p M H hpM) hj)
  haveI : Nontrivial (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ) := e.symm.toRingEquiv.toRingHom.domain_nontrivial
  haveI : Nonempty ↥(Spec (CommRingCat.of (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ)))
  have hI : AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ))) :=
    isIntegral_of_isOpenImmersion g
  have hD : IsDomain (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ) :=
    (affine_isIntegral_iff (CommRingCat.of (↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] κ))).mp hI
  exact MulEquiv.isDomain _ e.toMulEquiv

theorem ker_retraction_mem_minimalPrimes
    (F F' : Type) [Field F] [Algebra (R p) F] [Field F'] [Algebra (R p) F'] (j : F) [Fact (j ≠ 0)] (j' : F') [Fact (j' ≠ 0)]
    (κ : Type) [Field κ] [Algebra (R p) κ]
    [IsDomain (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F' j'))]
    (ι : ↥(TwoChartIntegralModel.chartAlgFin (R p) F' j') →ₐ[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))
    (hιj : ι (TwoChartIntegralModel.jChartFin (R p) F' j') = TwoChartIntegralModel.jChartFin (R p) F j)
    (σ₀ : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) →ₐ[κ] κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F' j'))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z) :
    RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) := by
  let φ : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F' j') →ₐ[κ] κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) ι
  haveI hP : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hK : (1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j ∈ φ.range :=
    φ.mem_range.2 ⟨(1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F' j', by
      show Algebra.TensorProduct.map (AlgHom.id κ κ) ι _ = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιj]⟩
  haveI : Algebra.IsIntegral ↥φ.range (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) :=
    ⟨fun z => isIntegral_of_mem F j κ φ.range hK z⟩
  have hcomap : (RingHom.ker σ₀.toRingHom).comap
      (algebraMap ↥φ.range (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨t, ht⟩ hmem
    obtain ⟨s, rfl⟩ := φ.mem_range.1 ht
    rw [Ideal.mem_comap, RingHom.mem_ker] at hmem
    change σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι s) = 0 at hmem
    rw [h0] at hmem
    subst hmem
    rw [Ideal.mem_bot]
    exact Subtype.ext (map_zero φ)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))) ≤ RingHom.ker σ₀.toRingHom)
  suffices hQP : Q = RingHom.ker σ₀.toRingHom by rw [← hQP]; exact hQ
  by_contra hne
  haveI : Q.IsPrime := hQ.1.1
  obtain ⟨-, x, hxP, hxQ⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hQle hne)
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥φ.range) hQle ⟨hxP, hxQ⟩
    (Algebra.IsIntegral.isIntegral x)
  rw [hcomap] at hlt
  exact not_lt_bot hlt

set_option maxHeartbeats 6400000 in

theorem eq_zero_of_forall_lift_apply_eq_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p)))
    (hθne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hset : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (Θ : Fin 2 → (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] LaurentSeries κ))
    (hΘ : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)),
      Θ i ((1 : κ) ⊗ₜ[R p] b) = (θ i b).map (ZMod.castHom (dvd_refl p) κ))
    (x : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (hx : ∀ i, Θ i x = 0) :
    x = 0 := by
  classical
  obtain ⟨hred, -⟩ :=
    ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH p M H hpM hpM2 hHp hj
  set I : Ideal ↥(chartAlgFin p (ΓM M H) hj) := Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))} with hI
  have hrad : I.radical = I := Ideal.radical_eq_iff.mpr ((Ideal.isRadical_iff_quotient_reduced I).mpr hred)
  have hker : ∀ b : ↥(chartAlgFin p (ΓM M H) hj), (∀ i, θ i b = 0) → b ∈ I := by
    intro b hb
    have hmem : ∀ 𝔮 ∈ I.minimalPrimes, b ∈ 𝔮 := by
      intro 𝔮 h𝔮
      rw [hset] at h𝔮
      rcases h𝔮 with rfl | rfl
      · exact hb 0
      · exact hb 1
    rw [← hrad, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    haveI := hJ
    obtain ⟨𝔮, h𝔮, h𝔮J⟩ := Ideal.exists_minimalPrimes_le hIJ
    exact h𝔮J (hmem 𝔮 h𝔮)
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  let B := Module.Basis.ofVectorSpace (ZMod p) κ
  have hι : (ZMod.castHom (dvd_refl p) κ : ZMod p →+* κ) = algebraMap (ZMod p) κ := RingHom.ext_zmod _ _
  have hlift : ∀ (c : ZMod p) (e : κ), ((c.val : ℕ) : R p) • e = c • e := by
    intro c e
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_natCast, ← hι, ZMod.castHom_apply, ZMod.cast_eq_val]
  have hrepr : ∀ y : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj),
      ∃ f : (Module.Basis.ofVectorSpaceIndex (ZMod p) κ) →₀ ↥(chartAlgFin p (ΓM M H) hj), y = f.sum (fun s o => (B s) ⊗ₜ[R p] o) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
        refine ⟨(B.repr a).mapRange (fun c => ((c.val : ℕ) : R p) • b) (by simp), ?_⟩
        rw [Finsupp.sum_mapRange_index (by intro s; simp)]
        conv_lhs => rw [← B.linearCombination_repr a]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.sum_tmul, Finsupp.sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← hlift, TensorProduct.smul_tmul]
    | add y z hy hz =>
        obtain ⟨f, rfl⟩ := hy
        obtain ⟨g, rfl⟩ := hz
        refine ⟨f + g, ?_⟩
        rw [Finsupp.sum_add_index']
        · intro s; simp
        · intro s o₁ o₂; rw [TensorProduct.tmul_add]
  obtain ⟨f, rfl⟩ := hrepr x
  have hzero : ∀ s ∈ f.support, ∀ i, θ i (f s) = 0 := by
    intro s hs i
    have h := hx i
    rw [Finsupp.sum, map_sum] at h
    have hC : ∀ a : κ, algebraMap κ (LaurentSeries κ) a = HahnSeries.single 0 a := fun a => by
      show HahnSeries.ofPowerSeries ℤ κ (PowerSeries.C a) = _
      exact HahnSeries.ofPowerSeries_C a
    have hterm : ∀ t, Θ i ((B t) ⊗ₜ[R p] f t) = HahnSeries.single 0 (B t) * (θ i (f t)).map (ZMod.castHom (dvd_refl p) κ) := by
      intro t
      rw [show (B t) ⊗ₜ[R p] f t = (algebraMap κ (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (B t)) * ((1 : κ) ⊗ₜ[R p] f t) by
            rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul, AlgHom.commutes, hΘ, hC]
    simp only [hterm] at h
    ext n
    have hn := congrArg (fun z : LaurentSeries κ => z.coeff n) h
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single_zero_mul, HahnSeries.map_coeff, HahnSeries.coeff_zero] at hn
    have hn' : ∑ t ∈ f.support, ((θ i (f t)).coeff n) • B t = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Algebra.smul_def, ← hι]; exact mul_comm _ _
    have hli := (linearIndependent_iff'.mp B.linearIndependent) f.support (fun t => (θ i (f t)).coeff n) hn' s hs
    simpa using hli
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero (fun s hs => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hker (f s) (hzero s hs))
  rw [← hc, show c * ((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj)) = ((p : ℕ) : R p) • c by
      rw [Algebra.smul_def, map_natCast]; exact mul_comm _ _,
    ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]

theorem eq_zero_of_reading_eq_zero (F : Type) [Field F] [Algebra (R p) F] (j : F) [Fact (j ≠ 0)]
    (κ : Type) [Field κ] [Algebra (R p) κ]
    [IsDomain (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))]
    (Θ' : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j) →+* LaurentSeries κ)
    (hC : ∀ a : κ, Θ' (algebraMap κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) a) = HahnSeries.C a)
    (hj : (Θ' ((1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j)).order < 0)
    (s : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) (hs : Θ' s = 0) : s = 0 := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subalgebra κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)),
      K = Algebra.adjoin κ {(1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j} := ⟨_, rfl⟩
  have hjK : (1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j ∈ K := by
    rw [hKdef]; exact Algebra.subset_adjoin (Set.mem_singleton _)
  haveI : Algebra.IsIntegral ↥K (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j)) :=
    ⟨fun z => isIntegral_of_mem F j κ K hjK z⟩
  haveI : (RingHom.ker Θ').IsPrime := RingHom.ker_isPrime _
  have hcomap : (RingHom.ker Θ').comap (algebraMap ↥K (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨k, hk⟩ hk0
    rw [Ideal.mem_comap, RingHom.mem_ker] at hk0
    change Θ' k = 0 at hk0
    have hk' : k ∈ Algebra.adjoin κ {(1 : κ) ⊗ₜ[R p] TwoChartIntegralModel.jChartFin (R p) F j} := hKdef ▸ hk
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hk'
    obtain ⟨P, rfl⟩ := hk'
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at hk0
    have hPC : Θ'.comp (algebraMap κ (κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))) = HahnSeries.C :=
      RingHom.ext hC
    rw [hPC] at hk0
    have hP0 : P = 0 := by
      by_contra hP
      exact eval₂_C_ne_zero _ hj P hP hk0
    rw [Ideal.mem_bot]
    apply Subtype.ext
    show Polynomial.aeval _ P = ((0 : ↥K) : κ ⊗[R p] ↥(TwoChartIntegralModel.chartAlgFin (R p) F j))
    rw [hP0, map_zero]
    rfl
  have hbot : RingHom.ker Θ' = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ↥K) hcomap
  have : s ∈ RingHom.ker Θ' := RingHom.mem_ker.mpr hs
  rw [hbot, Ideal.mem_bot] at this
  exact this

theorem coeffMap_injective {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

set_option maxHeartbeats 6400000 in

theorem ker_retraction_eq_ker_lift0
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    (θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p)))
    (hθ1 : ∀ c, θ 1 c = θ 0 (theta c))
    (hread : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      θ 0 c = coeffMap (GaloisRep.ratLocalizedAtResidue p) y)
    (hne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1))
    (hset : (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p)
    (Θt : Fin 2 → (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] LaurentSeries κ))
    (hΘ : ∀ i (a : κ) (c : ↥(chartAlgFin p (ΓM M H) hj)),
      Θt i (a ⊗ₜ[R p] c) = HahnSeries.C a * coeffMap (ZMod.castHom (dvd_refl p) κ) (θ i c))
    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    IsDomain (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∧
    RingHom.ker σ₀.toRingHom = RingHom.ker (Θt 0).toRingHom ∧
    RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ∧
    RingHom.ker (Θt 0).toRingHom ≠ RingHom.ker (Θt 1).toRingHom ∧
    minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) = {RingHom.ker (Θt 0).toRingHom, RingHom.ker (Θt 1).toRingHom} ∧
    (∀ 𝔓 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔓.IsPrime →
      RingHom.ker (Θt 0).toRingHom ≤ 𝔓 ∨ RingHom.ker (Θt 1).toRingHom ≤ 𝔓) ∧
    (∀ z, Θt 1 z = Θt 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom z)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hιinj : Function.Injective ι := ι.injective
  have hΘt : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)), Θt i ((1 : κ) ⊗ₜ[R p] b) = coeffMap ι (θ i b) := by
    intro i b
    rw [hΘ, map_one, one_mul]

  have hcomp : ∀ z, Θt 1 z = Θt 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a c =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply, hΘ, hΘ, hθ1]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

  set jN : ↥(chartAlgFin p (ΓN p M H hpM) hj) :=
    TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) with hjN
  set jM : ↥(chartAlgFin p (ΓM M H) hj) :=
    TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) with hjM
  have hιj : iota0 jN = jM := by
    apply Subtype.ext
    apply Subtype.ext
    rw [iota0_spec, hjN, hjM, TwoChartIntegralModel.coe_jChartFin, coe_jAt, TwoChartIntegralModel.coe_jChartFin, coe_jAt]

  have hθj : θ 0 (iota0 jN) = jqModC (ZMod p) := by
    rw [hread (iota0 jN) (jqModC (R p)), coeffMap_jqModC]
    rw [coeffMap_jqModC, iota0_spec, hjN, TwoChartIntegralModel.coe_jChartFin, coe_jAt]

  let gN : ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* LaurentSeries κ := ((coeffMap ι).comp (θ 0)).comp iota0.toRingHom
  have hgN : gN jN = jqModC κ := by
    show coeffMap ι (θ 0 (iota0 jN)) = _
    rw [hθj, coeffMap_jqModC]
  haveI : Nontrivial (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) :=
    (tensorRingHom (p := p) HahnSeries.C gN).domain_nontrivial
  haveI hdom : IsDomain (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) :=
    isDomain_tensor_chartAlgFin_gammaN p M H hpM hpM2 hj κ

  have hPmin : RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    ker_retraction_mem_minimalPrimes (p := p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
      (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) κ iota0 hιj σ₀ h0

  have hinj : ∀ x, (∀ i, Θt i x = 0) → x = 0 := fun x hx =>
    eq_zero_of_forall_lift_apply_eq_zero p M H hpM hpM2 hHp hj κ θ hne hset Θt hΘt x hx
  let Q : Fin 2 → Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := fun i => RingHom.ker (Θt i).toRingHom
  have hQprime : ∀ i, (Q i).IsPrime := fun i => RingHom.ker_isPrime _
  have hQinf : Q 0 ⊓ Q 1 = ⊥ := by
    refine le_bot_iff.mp (fun x hx => ?_)
    rw [Ideal.mem_bot]
    refine hinj x (fun i => ?_)
    fin_cases i
    · exact hx.1
    · exact hx.2
  have hcover : ∀ P' : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), P'.IsPrime → Q 0 ≤ P' ∨ Q 1 ≤ P' := by
    intro P' hP'
    refine hP'.mul_le.mp ?_
    exact (Ideal.mul_le_inf).trans (hQinf.le.trans bot_le)
  have hθmem : ∀ i (b : ↥(chartAlgFin p (ΓM M H) hj)), (1 : κ) ⊗ₜ[R p] b ∈ Q i ↔ θ i b = 0 := by
    intro i b
    rw [RingHom.mem_ker]
    change Θt i ((1 : κ) ⊗ₜ[R p] b) = 0 ↔ _
    rw [hΘt]
    constructor
    · intro h
      exact coeffMap_injective ι hιinj (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
  have hnotle : ∀ i i', i ≠ i' → ¬ Q i ≤ Q i' := by
    intro i i' hii' hle
    have hle' : RingHom.ker (θ i) ≤ RingHom.ker (θ i') := fun b hb => by
      rw [RingHom.mem_ker] at hb ⊢
      exact (hθmem i' b).mp (hle ((hθmem i b).mpr hb))
    have hθmin : ∀ k, RingHom.ker (θ k) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes := by
      intro k; fin_cases k
      · rw [hset]; exact Set.mem_insert _ _
      · rw [hset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hji : RingHom.ker (θ i') ≤ RingHom.ker (θ i) :=
      (hθmin i').2 ⟨(hθmin i).1.1, (hθmin i).1.2⟩ hle'
    have heq : RingHom.ker (θ i) = RingHom.ker (θ i') := le_antisymm hle' hji
    fin_cases i <;> fin_cases i'
    · exact hii' rfl
    · exact hne heq
    · exact hne heq.symm
    · exact hii' rfl
  have hQ01 : Q 0 ≠ Q 1 := fun h => hnotle 0 1 (by decide) h.le
  have hsetT : minimalPrimes (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) = {Q 0, Q 1} := by
    ext P'
    constructor
    · intro hP'
      rcases hcover P' hP'.1.1 with h0' | h1'
      · have := hP'.2 ⟨hQprime 0, bot_le⟩ h0'
        exact Or.inl (le_antisymm this h0')
      · have := hP'.2 ⟨hQprime 1, bot_le⟩ h1'
        exact Or.inr (le_antisymm this h1')
    · rintro (rfl | rfl)
      · refine ⟨⟨hQprime 0, bot_le⟩, ?_⟩
        rintro P' ⟨hP', -⟩ hle
        rcases hcover P' hP' with h0' | h1'
        · exact h0'
        · exact absurd (h1'.trans hle) (hnotle 1 0 (by decide))
      · refine ⟨⟨hQprime 1, bot_le⟩, ?_⟩
        rintro P' ⟨hP', -⟩ hle
        rcases hcover P' hP' with h0' | h1'
        · exact absurd (h0'.trans hle) (hnotle 0 1 (by decide))
        · exact h1'

  haveI hPprime : (RingHom.ker σ₀.toRingHom).IsPrime := hPmin.1.1
  have hu : θ 1 (jM - (theta.symm jM) ^ p) = 0 := by
    rw [map_sub, map_pow, hθ1, hθ1, AlgEquiv.apply_symm_apply, ← hιj, hfrob, sub_self]
  have hnot1 : ¬ Q 1 ≤ RingHom.ker σ₀.toRingHom := by
    intro hle
    have hmem : (1 : κ) ⊗ₜ[R p] (jM - (theta.symm jM) ^ p) ∈ Q 1 := (hθmem 1 _).mpr hu
    have hσ : σ₀ ((1 : κ) ⊗ₜ[R p] (jM - (theta.symm jM) ^ p)) = 0 := by
      have := hle hmem
      rw [RingHom.mem_ker] at this
      exact this
    rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at hσ
    have hl : σ₀ ((1 : κ) ⊗ₜ[R p] jM) = (1 : κ) ⊗ₜ[R p] jN := by
      rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[R p] jN), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hr : σ₀ ((1 : κ) ⊗ₜ[R p] ((theta.symm jM) ^ p)) = (σ₀ ((1 : κ) ⊗ₜ[R p] theta.symm jM)) ^ p := by
      rw [← map_pow σ₀, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [hl, hr] at hσ
    exact false_of_one_tmul_j_eq_pow (p := p) jN κ gN hgN _ hσ
  have h0le : Q 0 ≤ RingHom.ker σ₀.toRingHom := (hcover _ hPprime).resolve_right hnot1
  have hPeq : RingHom.ker σ₀.toRingHom = Q 0 := le_antisymm (hPmin.2 ⟨hQprime 0, bot_le⟩ h0le) h0le
  exact ⟨hdom, hPeq, hPmin, hQ01, hsetT, hcover, hcomp⟩

theorem exists_lift_pair (O : Type) [CommRing O] [Algebra (R p) O]
    (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    (θ : Fin 2 → (O →+* LaurentSeries (ZMod p))) :
    ∃ Θt : Fin 2 → (κ ⊗[R p] O →ₐ[κ] LaurentSeries κ),
      ∀ i (a : κ) (c : O), Θt i (a ⊗ₜ[R p] c) = HahnSeries.C a * coeffMap (ZMod.castHom (dvd_refl p) κ) (θ i c) := by
  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hextR : ∀ {S' : Type} [CommRing S'] (f g : R p →+* S'), f = g := fun f g => ringHom_ext_zp (p := p) f g
  let g : Fin 2 → (O →ₐ[R p] LaurentSeries κ) := fun i =>
    { (coeffMap ι).comp (θ i) with
      commutes' := fun r => by
        have h := hextR (((coeffMap ι).comp (θ i)).comp (algebraMap (R p) O)) (algebraMap (R p) (LaurentSeries κ))
        exact RingHom.congr_fun h r }
  have hg : ∀ i b, g i b = coeffMap ι (θ i b) := fun i b => rfl
  let f₀ : κ →ₐ[R p] LaurentSeries κ :=
    { algebraMap κ (LaurentSeries κ) with
      commutes' := fun r => RingHom.congr_fun (hextR
        ((algebraMap κ (LaurentSeries κ)).comp (algebraMap (R p) κ)) (algebraMap (R p) (LaurentSeries κ))) r }
  have hf₀ : ∀ a, f₀ a = algebraMap κ (LaurentSeries κ) a := fun a => rfl
  let Θ' : Fin 2 → (κ ⊗[R p] O →ₐ[R p] LaurentSeries κ) := fun i => Algebra.TensorProduct.productMap f₀ (g i)
  have hΘ' : ∀ i (a : κ) (b : O), Θ' i (a ⊗ₜ[R p] b) = algebraMap κ (LaurentSeries κ) a * coeffMap ι (θ i b) := by
    intro i a b
    simp only [Θ', Algebra.TensorProduct.productMap_apply_tmul, hf₀, hg]
  let Θt : Fin 2 → (κ ⊗[R p] O →ₐ[κ] LaurentSeries κ) := fun i =>
    { (Θ' i).toRingHom with
      commutes' := fun a => by
        show Θ' i (algebraMap κ (κ ⊗[R p] O) a) = algebraMap κ (LaurentSeries κ) a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        show Algebra.TensorProduct.productMap f₀ (g i) (a ⊗ₜ[R p] 1) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, hf₀] }
  refine ⟨Θt, fun i a b => ?_⟩
  show Θ' i (a ⊗ₜ[R p] b) = _
  rw [hΘ' i a b, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

set_option maxHeartbeats 6400000 in
theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∃ (Θ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ) (emb : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] LaurentSeries κ),
      Function.Injective emb ∧
      (∀ (a : κ) (c : ↥(chartAlgFin p (ΓM M H) hj)), emb (σ₀ (a ⊗ₜ[R p] c)) = HahnSeries.C a * Θ c) ∧
      (∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ℤ), coeffMap (Int.castRingHom ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        Θ c = coeffMap (Int.castRingHom κ) y) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨θ, hθ1, hread, hne, hset, hfrob, -⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta
  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  set jN : ↥(chartAlgFin p (ΓN p M H hpM) hj) :=
    TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) with hjN

  have hθj : θ 0 (iota0 jN) = jqModC (ZMod p) := by
    rw [hread (iota0 jN) (jqModC (R p)), coeffMap_jqModC]
    rw [coeffMap_jqModC, iota0_spec, hjN, TwoChartIntegralModel.coe_jChartFin, coe_jAt]

  obtain ⟨Θt, hΘC⟩ := exists_lift_pair (p := p) ↥(chartAlgFin p (ΓM M H) hj) κ θ
  have hΘt' : ∀ i (a : κ) (b : ↥(chartAlgFin p (ΓM M H) hj)),
      Θt i (a ⊗ₜ[R p] b) = algebraMap κ (LaurentSeries κ) a * coeffMap ι (θ i b) := by
    intro i a b
    rw [hΘC, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]

  obtain ⟨hdom, hPeq, -, -, -, -, -⟩ := ker_retraction_eq_ker_lift0 p M H hpM hpM2 hHp hj iota0 iota0_spec theta κ θ hθ1 hread hne hset
    hfrob Θt hΘC σ₀ h0
  haveI := hdom

  let φ : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) iota0
  have hφ : ∀ x b, φ (x ⊗ₜ[R p] b) = x ⊗ₜ[R p] iota0 b := fun x b => by
    show Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 _ = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have h0' : ∀ z, σ₀ (φ z) = z := h0
  have hfac : ∀ z, Θt 0 z = Θt 0 (φ (σ₀ z)) := fun z => by
    have hz : z - φ (σ₀ z) ∈ RingHom.ker σ₀.toRingHom := by
      rw [RingHom.mem_ker]
      show σ₀ (z - φ (σ₀ z)) = 0
      rw [map_sub, h0', sub_self]
    rw [hPeq, RingHom.mem_ker] at hz
    change Θt 0 (z - φ (σ₀ z)) = 0 at hz
    rwa [map_sub, sub_eq_zero] at hz

  let emb : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] LaurentSeries κ := (Θt 0).comp φ
  have hembt : ∀ x b, emb (x ⊗ₜ[R p] b) = algebraMap κ (LaurentSeries κ) x * coeffMap ι (θ 0 (iota0 b)) := by
    intro x b
    show Θt 0 (φ (x ⊗ₜ[R p] b)) = _
    rw [hφ, hΘt']
  have hC : ∀ a : κ, emb.toRingHom (algebraMap κ (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) a) = HahnSeries.C a := by
    intro a
    show emb (algebraMap κ (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) a) = HahnSeries.C a
    rw [AlgHom.commutes, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  have hjord : (emb.toRingHom ((1 : κ) ⊗ₜ[R p] jN)).order < 0 := by
    show (emb ((1 : κ) ⊗ₜ[R p] jN)).order < 0
    rw [hembt, map_one, one_mul, hθj, coeffMap_jqModC, order_jqModC]
    norm_num
  have hinj : Function.Injective emb := by
    intro s t hst
    have h := eq_zero_of_reading_eq_zero (p := p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) κ
      emb.toRingHom hC hjord (s - t) (by show emb (s - t) = 0; rw [map_sub, hst, sub_self])
    exact sub_eq_zero.mp h

  refine ⟨(coeffMap ι).comp (θ 0), emb, hinj, ?_, ?_⟩
  · intro a c
    show Θt 0 (φ (σ₀ (a ⊗ₜ[R p] c))) = HahnSeries.C a * coeffMap ι (θ 0 c)
    rw [← hfac, hΘt', algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
  · intro c y hy
    show coeffMap ι (θ 0 c) = coeffMap (Int.castRingHom κ) y
    have hy' : coeffMap (algebraMap (R p) ℚ) (coeffMap (Int.castRingHom (R p)) y) =
        (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
      rw [coeffMap_coeffMap, ← hy]
      exact coeffMap_congr (RingHom.ext_int _ _) y
    rw [hread c _ hy', coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) y

end RetrMinH

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∃ (Θ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ) (emb : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] LaurentSeries κ),
      Function.Injective emb ∧
      (∀ (a : κ) (c : ↥(chartAlgFin p (ΓM M H) hj)), emb (σ₀ (a ⊗ₜ[R p] c)) = HahnSeries.C a * Θ c) ∧
      (∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ℤ), coeffMap (Int.castRingHom ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        Θ c = coeffMap (Int.castRingHom κ) y) := by
  exact RetrMinH.main p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta κ σ₀ h0

end
end S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH (solution)
