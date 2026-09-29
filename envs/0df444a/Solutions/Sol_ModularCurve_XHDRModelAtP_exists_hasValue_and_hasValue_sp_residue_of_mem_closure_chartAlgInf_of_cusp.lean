-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b1e08503-94d3-53ba-aa07-406cd4289f74

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_eq_specMap_comp_iotaInf_of_isCuspidal_of_section
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_isZeroSide_of_isCuspidal_of_section_comp_one
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace ValDictBlr

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_nonunits_iff_mem_and (O : ValuationSubring F) (x : F) :
    x ∈ O.nonunits ↔ x ∈ O ∧ (x = 0 ∨ x⁻¹ ∉ O) := by
  constructor
  · intro hx
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
    refine ⟨hmem, ?_⟩
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      intro hinv
      have hu : IsUnit (⟨x, hmem⟩ : O) :=
        ⟨⟨⟨x, hmem⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  · rintro ⟨hmem, h⟩
    apply ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    refine ⟨hmem, (IsLocalRing.mem_maximalIdeal _).mpr ?_⟩
    intro hu
    rcases h with h0 | hinv
    · apply hu.ne_zero
      exact Subtype.ext h0
    · apply hinv
      obtain ⟨u, hu'⟩ := hu
      have h1 : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
      have h2 : (((u⁻¹ : Oˣ) : O) : F) * x = 1 := by
        have := congrArg (fun z : O => (z : F)) h1
        simpa [hu'] using this
      have h3 : (((u⁻¹ : Oˣ) : O) : F) = x⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [← h3]
      exact ((u⁻¹ : Oˣ) : O).2

theorem residue_algebraMap_eq (v : Place K F) (a : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ = algebraMap K v.ResidueField a := by
  obtain ⟨h, hr⟩ := v.hasValue_algebraMap a
  exact hr

theorem hasValue_iff_sub_mem_nonunits (v : Place K F) (g : F) (a : K) :
    v.HasValue g a ↔ g - algebraMap K F a ∈ v.toValuationSubring.nonunits := by
  constructor
  · rintro ⟨hg, hr⟩
    apply ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    refine ⟨sub_mem hg (v.algebraMap_mem' a), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap K F a, sub_mem hg (v.algebraMap_mem' a)⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := Subtype.ext rfl
    rw [this, map_sub, hr, residue_algebraMap_eq, sub_self]
  · intro hn
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hn
    have hg : g ∈ v.toValuationSubring := by
      have : g = (g - algebraMap K F a) + algebraMap K F a := by ring
      rw [this]; exact add_mem hmem (v.algebraMap_mem' a)
    refine ⟨hg, ?_⟩
    have hz : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F a, hmem⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    have : (⟨g, hg⟩ : v.toValuationSubring) = ⟨g - algebraMap K F a, hmem⟩ + ⟨algebraMap K F a, v.algebraMap_mem' a⟩ :=
      Subtype.ext (by simp)
    rw [this, map_add, hz, zero_add, residue_algebraMap_eq]

theorem HasValue.add' (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := Subtype.ext rfl
  rw [this, map_add, hr, hr', map_add]

theorem hasValue_zero' (v : Place K F) : v.HasValue (0 : F) 0 := by
  have := v.hasValue_algebraMap (0 : K)
  rwa [map_zero] at this

theorem HasValue.neg' (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  have := (v.hasValue_algebraMap (-1 : K)).mul h
  rwa [map_neg, map_one, neg_one_mul, neg_one_mul] at this

theorem HasValue.pow' (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem mem_restrictAlong_iff' {F' : Type*} [Field F'] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring := by
  rw [show (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom from rfl,
    ValuationSubring.mem_comap]
  exact Iff.rfl

theorem hasValue_restrictAlong_iff {F' : Type*} [Field F'] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (g : F) (a : K) :
    (w.restrictAlong φ hφ).HasValue g a ↔ w.HasValue (φ g) a := by
  rw [hasValue_iff_sub_mem_nonunits, hasValue_iff_sub_mem_nonunits, mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and,
    mem_restrictAlong_iff', mem_restrictAlong_iff', map_inv₀, map_sub, AlgHom.commutes]
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hiff : g - algebraMap K F a = 0 ↔ φ g - algebraMap K F' a = 0 := by
    rw [← AlgHom.commutes φ a, ← map_sub]
    exact ⟨fun h => by rw [h, map_zero], fun h => hinj (by rw [h, map_zero])⟩
  rw [hiff]

def valRing (W : Place K F) (A : ValuationSubring K) : Subring F where
  carrier := {f | ∃ a : K, a ∈ A ∧ W.HasValue f a}
  mul_mem' := by
    rintro f g ⟨a, ha, hf⟩ ⟨b, hb, hg⟩
    exact ⟨a * b, mul_mem ha hb, hf.mul hg⟩
  one_mem' := ⟨1, one_mem _, W.hasValue_one⟩
  add_mem' := by
    rintro f g ⟨a, ha, hf⟩ ⟨b, hb, hg⟩
    exact ⟨a + b, add_mem ha hb, HasValue.add' W hf hg⟩
  zero_mem' := ⟨0, zero_mem _, hasValue_zero' W⟩
  neg_mem' := by
    rintro f ⟨a, ha, hf⟩
    exact ⟨-a, neg_mem ha, HasValue.neg' W hf⟩

theorem mem_valRing_iff (W : Place K F) (A : ValuationSubring K) (f : F) :
    f ∈ valRing W A ↔ ∃ a : K, a ∈ A ∧ W.HasValue f a := Iff.rfl

theorem mem_valRing_of_isIntegral (W : Place K F) (hW : Function.Surjective (algebraMap K W.ResidueField)) (A : ValuationSubring K)
    {f : F} (hf : IsIntegral ↥(valRing W A) f) : f ∈ valRing W A := by
  classical
  obtain ⟨P, hPm, hP⟩ := hf
  have hcoefO : ∀ t : ↥(valRing W A), ((t : F)) ∈ W.toValuationSubring := fun t => by
    obtain ⟨a, -, ha⟩ := t.2; exact ha.mem

  have hfO : f ∈ W.toValuationSubring := by
    let g' : ↥(valRing W A) →+* W.toValuationSubring := (valRing W A).subtype.codRestrict W.toValuationSubring hcoefO
    have hcomp : (algebraMap W.toValuationSubring F).comp g' = (valRing W A).subtype := RingHom.ext fun t => rfl
    have hint : IsIntegral W.toValuationSubring f := by
      refine ⟨P.map g', hPm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hcomp]
      exact hP
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]; exact y.2

  obtain ⟨c, hc⟩ := hW (IsLocalRing.residue W.toValuationSubring ⟨f, hfO⟩)
  have hfc : W.HasValue f c := ⟨hfO, hc.symm⟩

  let ev : ↥(valRing W A) → K := fun t => (t.2).choose
  have hev : ∀ t : ↥(valRing W A), ev t ∈ A ∧ W.HasValue (t : F) (ev t) := fun t => (t.2).choose_spec
  let evHom : ↥(valRing W A) →+* K :=
    { toFun := ev
      map_one' := ((hev 1).2.unique (by simpa using W.hasValue_one))
      map_mul' := fun s t => ((hev (s * t)).2.unique (by simpa using (hev s).2.mul (hev t).2))
      map_zero' := ((hev 0).2.unique (by simpa using hasValue_zero' W))
      map_add' := fun s t => ((hev (s + t)).2.unique (by simpa using HasValue.add' W (hev s).2 (hev t).2)) }
  have hevHom : ∀ t, evHom t = ev t := fun _ => rfl

  have hval : ∀ Q : Polynomial ↥(valRing W A),
      W.HasValue (Polynomial.eval₂ (valRing W A).subtype f Q) ((Q.map evHom).eval c) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.eval₂_add, Polynomial.map_add, Polynomial.eval_add]
      exact HasValue.add' W hp hq
    | monomial n t =>
      rw [Polynomial.eval₂_monomial, Polynomial.map_monomial, Polynomial.eval_monomial, hevHom]
      exact (hev t).2.mul (HasValue.pow' W hfc n)
  have hroot : (P.map evHom).eval c = 0 := by
    have h := hval P
    rw [show Polynomial.eval₂ (valRing W A).subtype f P = 0 from hP] at h
    exact ((hasValue_zero' W).unique h).symm

  let evA : ↥(valRing W A) →+* ↥A := evHom.codRestrict A.toSubring (fun t => (hev t).1)
  have hcomp : (A.subtype : ↥A →+* K).comp evA = evHom := RingHom.ext fun t => rfl
  have hcint : IsIntegral ↥A c := by
    refine ⟨P.map evA, hPm.map evA, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((A.subtype : ↥A →+* K).comp evA) c P = 0
    rw [hcomp, ← Polynomial.eval_map, hroot]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  refine ⟨c, ?_, hfc⟩
  rw [← hy]; exact y.2

end Generic

section Kit

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

theorem algebraMap_residueField_surjective (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) := by
  haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2

theorem coeff_neg_one_jqModC' (K : Type*) [Field K] : (jqModC K).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]

theorem ord_pos_of_mem_nonunits' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring.nonunits) (hf0 : f ≠ 0) : 0 < v.ord f := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hf
  have h0 : 0 ≤ v.ord f := v.ord_nonneg_of_mem hmem
  have hne : v.ord f ≠ 0 := by
    intro h
    have h1 : v.adicValuation f = 1 := (v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h
    have hu : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := (v.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  omega

theorem exists_hasValue_inv_of_isCuspidal (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W)
    (jM : ↥(xHFunctionFieldBar M H)) (hjM : ((jM : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ W.HasValue jM⁻¹ a := by
  have hjM0 : jM ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
    simp only [hjM, coeff_neg_one_jqModC'] at h1
    simp at h1
  by_cases hO : jM ∈ W.toValuationSubring
  ·
    obtain ⟨c, hc⟩ := algebraMap_residueField_surjective W (IsLocalRing.residue W.toValuationSubring ⟨jM, hO⟩)
    have hval : W.HasValue jM c := ⟨hO, hc.symm⟩
    have hcA : c ∉ A := by
      intro hcA
      have hle := hW jM hjM ⟨c, hcA⟩
      have hnu := (hasValue_iff_sub_mem_nonunits W jM c).mp hval
      have hne : jM - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ≠ 0 := by
        intro h
        have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) (sub_eq_zero.mp h)
        simp only [hjM, coeff_neg_one_jqModC'] at h1
        rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
            = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c from rfl,
          algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by decide)] at h1
        exact one_ne_zero h1
      have hpos := ord_pos_of_mem_nonunits' W hnu hne
      exact absurd hle (not_le.mpr (by exact_mod_cast hpos))
    have hc0 : c ≠ 0 := fun h => hcA (h ▸ zero_mem A)
    refine ⟨c⁻¹, ?_, hval.inv hc0⟩
    rcases A.mem_or_inv_mem c with h | h
    · exact absurd h hcA
    · exact h
  ·
    refine ⟨0, zero_mem A, ?_⟩
    rw [hasValue_iff_sub_mem_nonunits, map_zero, sub_zero, mem_nonunits_iff_mem_and]
    refine ⟨?_, Or.inr (by rwa [inv_inv])⟩
    rcases W.toValuationSubring.mem_or_inv_mem jM with h | h
    · exact absurd h hO
    · exact h

theorem exists_hasValue_alpha_of_mem_integralOverPoleChart_of_isCuspidal
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W)
    (b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) :
    ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ W.HasValue (α b) a := by
  classical
  letI instA : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))).comp A.subtype).toAlgebra

  have hgen : ∀ s ∈ Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))), α s ∈ valRing W A := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [map_inv₀]
      obtain ⟨a, ha, hv⟩ := exists_hasValue_inv_of_isCuspidal A W hW (α x') (by rw [hα_coe, hx'])
      exact ⟨a, ha, hv⟩
    | algebraMap r =>
      refine ⟨(r : AlgebraicClosure ℚ), r.2, ?_⟩
      show W.HasValue (α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (r : AlgebraicClosure ℚ))) (r : AlgebraicClosure ℚ)
      rw [AlgHom.commutes]
      exact W.hasValue_algebraMap _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

  set S₀ := Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) with hS₀
  obtain ⟨P, hPm, hP⟩ : IsIntegral ↥S₀ b := hb
  let ψ : ↥S₀ →+* ↥(valRing W A) := (α.toRingHom.comp S₀.toSubring.subtype).codRestrict (valRing W A) (fun s => hgen s s.2)
  have hcomp : (valRing W A).subtype.comp ψ = α.toRingHom.comp (algebraMap ↥S₀ ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) := RingHom.ext fun s => rfl
  have hint : IsIntegral ↥(valRing W A) (α b) := by
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((valRing W A).subtype.comp ψ) (α b) P = 0
    rw [hcomp, show α b = α.toRingHom b from rfl, ← Polynomial.hom_eval₂, hP, map_zero]
  exact mem_valRing_of_isIntegral W (algebraMap_residueField_surjective W) A hint

end Kit

section Corollary

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

theorem exists_hasValue_of_mem_integralOverPoleChart_of_forall_ord_sub_nonpos
    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x'))
    (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hw : ∀ a : ↥A, w.ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ a : ↥A, w.HasValue b (a : AlgebraicClosure ℚ) ∧
      ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.restrictAlong α hα = w ∧
        (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W ∧ W.HasValue (α b) (a : AlgebraicClosure ℚ) := by
  haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1

  have hw' : ∀ x : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((x : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ a : ↥A, w.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro x hx a
    have : x = x' := Subtype.ext (hx.trans hx'.symm)
    rw [this]; exact hw a
  obtain ⟨W, hWw, hWinf⟩ :=
    ModularCurve.JHPlaceSpecialization.exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos p M H hpM hpM2 hHp A hA α hα hα_coe w hw'
  obtain ⟨a, haA, hval⟩ := exists_hasValue_alpha_of_mem_integralOverPoleChart_of_isCuspidal (p := p) A α hα_coe x' hx' W hWinf.1 b hb
  refine ⟨⟨a, haA⟩, ?_, W, hWw, hWinf, hval⟩
  rw [← hWw, hasValue_restrictAlong_iff]
  exact hval

end Corollary

section GenericValue

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem hasValue_pointEquivPlace_of_coe_eq_coeffEmb_of_eq_specMap_comp_iotaInf
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (ψ : ↥(chartAlgInf p (ΓM M H) hj) →+* ↥A) (hψ : u.1 = Spec.map (CommRingCat.ofHom ψ) ≫ ιInf p (ΓM M H) hj)
    (c : ↥(chartAlgInf p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H))
    (hf : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) :
    (𝔛.Meta.pointEquivPlace y).HasValue f ((ψ c : ↥A) : AlgebraicClosure ℚ) := by
  haveI := 𝔛.eeta_iso
  obtain ⟨hne, hread⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb p M H hpM hj 𝔛 c
  haveI := hne
  have hy : y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (A.subtype.comp ψ)) ≫ ιInf p (ΓM M H) hj := by
    rw [← hu, hψ, ← Category.assoc, barPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hval := 𝔛.Meta.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
    (𝔛.eeta ≫ pullback.fst _ _) (ιInf p (ΓM M H) hj) y (A.subtype.comp ψ) hy c

  have hrf : 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField
      ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
      (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv c)))) = f :=
    Subtype.ext (hread.trans hf.symm)
  rw [hrf] at hval
  exact (hasValue_iff_sub_mem_nonunits _ f _).mpr (by simpa [RingHom.comp_apply] using hval)

end GenericValue

section SpecialValue

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem hasValue_placeOfPoint_of_section_comp_zero
    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (ψ : ↥(chartAlgInf p (ΓM M H) hj) →+* ↥A) (hψ : u.1 = Spec.map (CommRingCat.ofHom ψ) ≫ ιInf p (ΓM M H) hj)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (c : ↥(chartAlgInf p (ΓM M H) hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))
    (g : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) (hg : ((g : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y) :
    ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0).HasValue g (IsLocalRing.residue ↥A (ψ c)) := by
  haveI := 𝔛.efib_iso A hA ρ hρ
  haveI := 𝔛.lfp
  set F := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) with hF
  obtain ⟨hne, hread⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ c
  haveI := hne

  set z : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _} := (pointEquivClosedPoint (𝔛.Mfib A hA ρ hρ).toBase).symm P0 with hz_def
  have hzP0 : pointEquivClosedPoint (𝔛.Mfib A hA ρ hρ).toBase z = P0 := Equiv.apply_symm_apply _ _
  have hzpt : z.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) = P0.1 := congrArg Subtype.val hzP0

  have hsec : z.1 ≫ 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 = uκ := by
    apply AlgebraicGeometry.ext_of_apply_closedPoint_eq (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    · rw [Category.assoc, Category.assoc, 𝔛.comp_over A hA ρ hρ 0, 𝔛.hefib A hA ρ hρ]
      exact z.2
    · exact huκ₂
    · simp only [Scheme.Hom.comp_base, TopCat.comp_app]
      rw [hzpt]
      simpa [Scheme.Hom.comp_base, TopCat.comp_app] using hP0
  have hzF : z.1 ≫ F = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ψ)) ≫ ιInf p (ΓM M H) hj := by
    rw [hF, ← Category.assoc, ← Category.assoc, Category.assoc z.1, hsec, huκ₁, hψ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hval := (𝔛.Mfib A hA ρ hρ).ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
    F (ιInf p (ΓM M H) hj) z ((IsLocalRing.residue ↥A).comp ψ) hzF c

  have hrg : (𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (F ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
      ((F.app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓM M H) hj).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv c)))) = g :=
    Subtype.ext ((hread y hy).trans hg.symm)
  rw [hrg, CurveModel.pointEquivPlace_apply, hzP0] at hval
  exact (hasValue_iff_sub_mem_nonunits _ g _).mpr (by simpa [RingHom.comp_apply] using hval)

end SpecialValue

section Generators

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem exists_mem_integers_coe_residue_eq
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)} {Psp : JHPlaceSpecialization p M H hpM A}
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (yA : LaurentSeries ↥A) (f : ↥(xHFunctionFieldBar M H)) (hf : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype yA) :
    ∃ h : f ∈ Rpd.R₁.integers, ((Rpd.R₁.residue ⟨f, h⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) yA := by
  have hmem : coeffMap A.subtype yA ∈ xHFunctionFieldBar M H := by rw [← hf]; exact f.2
  obtain ⟨hO, hres⟩ := Rpd.residue₁_coeffMap yA hmem
  have e : (⟨coeffMap A.subtype yA, hmem⟩ : ↥(xHFunctionFieldBar M H)) = f := Subtype.ext hf.symm
  subst e
  exact ⟨hO, hres⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem hasValue_and_hasValue_residue_of_coe_eq_coeffEmb
    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)} {Psp : JHPlaceSpecialization p M H hpM A}
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (ψ : ↥(chartAlgInf p (ΓM M H) hj) →+* ↥A) (hψ : u.1 = Spec.map (CommRingCat.ofHom ψ) ≫ ιInf p (ΓM M H) hj)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (c : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hbc : ((b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) :
    (𝔛.Meta.pointEquivPlace y).HasValue (α b) ((ψ (𝔛.iotaInf c) : ↥A) : AlgebraicClosure ℚ) ∧
      ∃ h : α b ∈ Rpd.R₁.integers,
        ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0).HasValue (Rpd.R₁.residue ⟨α b, h⟩) (IsLocalRing.residue ↥A (ψ (𝔛.iotaInf c))) := by

  have hf : ((α b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((𝔛.iotaInf c : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
    rw [hα_coe, hbc, 𝔛.iotaInf_spec]
  refine ⟨hasValue_pointEquivPlace_of_coe_eq_coeffEmb_of_eq_specMap_comp_iotaInf 𝔛 A ρ y u hu ψ hψ (𝔛.iotaInf c) (α b) hf, ?_⟩

  obtain ⟨yR, hyR⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt (ΓN p M H hpM) hj)).2 c
  have halg : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) :=
    (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)).symm
  have hyA : ((α b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (coeffMap ρ yR) := by
    rw [hα_coe, hbc, ← hyR, coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap, hρ, halg]
  obtain ⟨h, hres⟩ := exists_mem_integers_coe_residue_eq Rpd (coeffMap ρ yR) (α b) hyA
  refine ⟨h, ?_⟩
  have hg : ((Rpd.R₁.residue ⟨α b, h⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap ((IsLocalRing.residue ↥A).comp ρ) yR := by
    rw [hres, coeffMap_coeffMap]
  have hyM : coeffMap (algebraMap (R p) ℚ) yR = (((𝔛.iotaInf c : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
    rw [hyR, 𝔛.iotaInf_spec]
  exact hasValue_placeOfPoint_of_section_comp_zero hpM2 hHp 𝔛 A hA ρ hρ u ψ hψ uκ huκ₁ huκ₂ P0 hP0 (𝔛.iotaInf c) yR hyM _ hg

end Generators

end ValDictBlr

open ValDictBlr

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hB : ∀ b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})), α b ∈ Rpd.R₁.integers)
    (b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hb : b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})))
    (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hw : ∀ a : ↥A, w.ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ a : ↥A, w.HasValue b (a : AlgebraicClosure ℚ) ∧
      (Psp.sp w).HasValue (Rpd.R₁.residue ⟨α b, hB b hb⟩) (IsLocalRing.residue ↥A a) := by
  classical
  haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI := 𝔛.eeta_iso

  have hw' : ∀ x : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((x : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ a : ↥A, w.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro x hx a
    have : x = x' := Subtype.ext (hx.trans hx'.symm)
    rw [this]; exact hw a
  obtain ⟨W, hWw, hWinf⟩ :=
    ModularCurve.JHPlaceSpecialization.exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos p M H hpM hpM2 hHp A hA α hα hα_coe w hw'

  set yg := 𝔛.Meta.pointEquivPlace.symm W with hyg_def
  have hW : 𝔛.Meta.pointEquivPlace yg = W := Equiv.apply_symm_apply _ _
  obtain ⟨u, hu, uκ, huκ₁, huκ₂, i, P0, hP0⟩ :=
    ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq p M H hpM hj 𝔛 A hA ρ hρ yg
  have hcusp : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace yg) := by
    rw [hW]; exact hWinf.1
  have hi : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | n, hn⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases hi with rfl | rfl
  swap
  · exfalso
    have hz := ModularCurve.XHDRModelAtP.isZeroSide_of_isCuspidal_of_section_comp_one p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      yg u hu uκ huκ₁ huκ₂ P0 hP0 hcusp
    rw [hW] at hz
    exact ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA W hz hWinf

  obtain ⟨ψ, hψ⟩ := ModularCurve.XHDRModelAtP.exists_eq_specMap_comp_iotaInf_of_isCuspidal_of_section p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
    yg u hu hcusp

  have hsp : Psp.sp w = (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 := by
    have h := hcomp 0 yg u hu uκ huκ₁ huκ₂ P0 hP0
    rw [if_pos rfl, hW] at h
    rw [← hWw]
    exact h.symm

  have key : ∀ b' ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})),
      ∃ a : ↥A, W.HasValue (α b') (a : AlgebraicClosure ℚ) ∧ ∃ h : α b' ∈ Rpd.R₁.integers,
        ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0).HasValue (Rpd.R₁.residue ⟨α b', h⟩) (IsLocalRing.residue ↥A a) := by

    have hcst : ∀ a : ↥A, ∃ a₀ : ↥A, W.HasValue (α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ))) (a₀ : AlgebraicClosure ℚ) ∧
        ∃ h : α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ∈ Rpd.R₁.integers,
          ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0).HasValue (Rpd.R₁.residue ⟨_, h⟩) (IsLocalRing.residue ↥A a₀) := by
      intro a
      refine ⟨a, ?_, ?_⟩
      · rw [AlgHom.commutes]; exact W.hasValue_algebraMap _
      · have hmem : α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ∈ Rpd.R₁.integers := by
          rw [AlgHom.commutes]; exact (Rpd.R₁.algebraMap_mem_iff _).mpr a.2
        refine ⟨hmem, ?_⟩
        have : Rpd.R₁.residue ⟨_, hmem⟩ = algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) (IsLocalRing.residue ↥A a) := by
          rw [← Rpd.R₁.residue_algebraMap a]
          congr 1
          exact Subtype.ext (AlgHom.commutes α _)
        rw [this]
        exact ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0).hasValue_algebraMap _
    intro b' hb'
    induction hb' using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨c, hc⟩
      · exact hcst a
      · obtain ⟨hv, h, hsv⟩ := hasValue_and_hasValue_residue_of_coe_eq_coeffEmb hpM2 hHp 𝔛 A hA ρ hρ Rpd α hα_coe yg u hu ψ hψ uκ huκ₁ huκ₂ P0 hP0 c x hc
        rw [hW] at hv
        exact ⟨ψ (𝔛.iotaInf c), hv, h, hsv⟩
    | zero => simpa using hcst 0
    | one => simpa using hcst 1
    | add x y _ _ hx hy =>
      obtain ⟨a₁, hv₁, h₁, hs₁⟩ := hx
      obtain ⟨a₂, hv₂, h₂, hs₂⟩ := hy
      refine ⟨a₁ + a₂, ?_, ?_⟩
      · rw [map_add]; push_cast; exact HasValue.add' W hv₁ hv₂
      · have hmem : α (x + y) ∈ Rpd.R₁.integers := by rw [map_add]; exact add_mem h₁ h₂
        refine ⟨hmem, ?_⟩
        have : (⟨α (x + y), hmem⟩ : Rpd.R₁.integers) = ⟨α x, h₁⟩ + ⟨α y, h₂⟩ := Subtype.ext (map_add α x y)
        rw [this, map_add, map_add]
        exact HasValue.add' _ hs₁ hs₂
    | neg x _ hx =>
      obtain ⟨a, hv, h, hs⟩ := hx
      refine ⟨-a, ?_, ?_⟩
      · rw [map_neg]; push_cast; exact HasValue.neg' W hv
      · have hmem : α (-x) ∈ Rpd.R₁.integers := by rw [map_neg]; exact neg_mem h
        refine ⟨hmem, ?_⟩
        have : (⟨α (-x), hmem⟩ : Rpd.R₁.integers) = -⟨α x, h⟩ := Subtype.ext (map_neg α x)
        rw [this, map_neg, map_neg]
        exact HasValue.neg' _ hs
    | mul x y _ _ hx hy =>
      obtain ⟨a₁, hv₁, h₁, hs₁⟩ := hx
      obtain ⟨a₂, hv₂, h₂, hs₂⟩ := hy
      refine ⟨a₁ * a₂, ?_, ?_⟩
      · rw [map_mul]; push_cast; exact hv₁.mul hv₂
      · have hmem : α (x * y) ∈ Rpd.R₁.integers := by rw [map_mul]; exact mul_mem h₁ h₂
        refine ⟨hmem, ?_⟩
        have : (⟨α (x * y), hmem⟩ : Rpd.R₁.integers) = ⟨α x, h₁⟩ * ⟨α y, h₂⟩ := Subtype.ext (map_mul α x y)
        rw [this, map_mul, map_mul]
        exact hs₁.mul hs₂
  obtain ⟨a, hWval, h, hspval⟩ := key b hb
  refine ⟨a, ?_, ?_⟩
  · rw [← hWw, ValDictBlr.hasValue_restrictAlong_iff]
    exact hWval
  · rw [hsp]
    exact hspval

end S_ModularCurve_XHDRModelAtP_exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp (solution)
