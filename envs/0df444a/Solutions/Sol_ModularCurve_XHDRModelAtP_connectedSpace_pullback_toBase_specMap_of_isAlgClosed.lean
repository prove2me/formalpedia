-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/614d929e-208b-5f76-a35e-ad667eaf619a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

p2m_open "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace XHChartConstants

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (j : ↥(qExpFunctionFieldC ℚ Γ))

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt p)
set_option quotPrecheck false in
local notation "F" => ↥(qExpFunctionFieldC ℚ Γ)

set_option synthInstance.maxHeartbeats 1600000 in

theorem mem_valuationSubring_of_mem_chartAlg {S : Set F} {x : F} (hx : x ∈ chartAlg ℤℓ F S)
    (V : ValuationSubring F) (hV : Set.range (algebraMap ℤℓ F) ⊆ V) (hS : S ⊆ V) : x ∈ V := by
  let V' : Subalgebra ℤℓ F :=
    { V.toSubring with
      algebraMap_mem' := fun r => hV ⟨r, rfl⟩ }
  have hadj : Algebra.adjoin ℤℓ S ≤ V' := Algebra.adjoin_le hS
  have hint : IsIntegral V' x := by
    rw [mem_chartAlg_iff] at hx
    exact hx.map_of_comp_eq (Subalgebra.inclusion hadj).toRingHom (RingHom.id F) (by ext; rfl)

  have hint' : IsIntegral V x := by
    obtain ⟨P, hP, hPx⟩ := hint
    refine ⟨P.map (RingEquiv.subringCongr (rfl : (V'.toSubring : Subring F) = V.toSubring)).toRingHom,
      hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hPx using 2 <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _
  haveI : IsIntegrallyClosedIn V F := inferInstanceAs (IsIntegrallyClosedIn V F)
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hint'
  rw [← hy]
  exact y.2

set_option synthInstance.maxHeartbeats 1600000 in
theorem isIntegral_of_mem_of_mem {x : F} (hx0 : x ∈ chartAlgFin ℤℓ F j) (hx1 : x ∈ chartAlgInf ℤℓ F j) :
    IsIntegral ℤℓ x := by
  have hmem : x ∈ (⨅ V : {V : ValuationSubring F // Set.range (algebraMap ℤℓ F) ⊆ V.toSubring},
      V.1.toSubring) := by
    refine Subring.mem_iInf.mpr fun V => ?_
    rcases V.1.mem_or_inv_mem j with hj | hj
    · exact mem_valuationSubring_of_mem_chartAlg p Γ hx0 V.1 V.2 (Set.singleton_subset_iff.mpr hj)
    · exact mem_valuationSubring_of_mem_chartAlg p Γ hx1 V.1 V.2 (Set.singleton_subset_iff.mpr hj)
  rw [iInf_valuationSubring_superset] at hmem
  have hcl : Subring.closure (Set.range (algebraMap ℤℓ F)) = (algebraMap ℤℓ F).range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  have hint : IsIntegral (Subring.closure (Set.range (algebraMap ℤℓ F))) x := hmem
  obtain ⟨P, hP, hPx⟩ := hint

  let f : ℤℓ →+* Subring.closure (Set.range (algebraMap ℤℓ F)) :=
    (algebraMap ℤℓ F).codRestrict _ (fun r => Subring.subset_closure ⟨r, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hcl] at hy
    obtain ⟨r, rfl⟩ := hy
    exact ⟨r, Subtype.ext rfl⟩
  have hlifts : P ∈ Polynomial.lifts f := P.lifts_iff_coeff_lifts.mpr fun i => hf _
  obtain ⟨Q, hQP, -, hQmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hP
  refine ⟨Q, hQmonic, ?_⟩
  have hcomp : (algebraMap (Subring.closure (Set.range (algebraMap ℤℓ F))) F).comp f = algebraMap ℤℓ F := by
    ext r; rfl
  rw [← hcomp, ← Polynomial.eval₂_map, hQP, hPx]

set_option synthInstance.maxHeartbeats 1600000 in
theorem exists_eq_algebraMap {x : F} (hx0 : x ∈ chartAlgFin ℤℓ F j) (hx1 : x ∈ chartAlgInf ℤℓ F j) :
    ∃ r : ℤℓ, x = algebraMap ℚ F (r : ℚ) := by
  have hint := isIntegral_of_mem_of_mem p Γ j hx0 hx1

  have hintQ : IsIntegral ℚ x := hint.tower_top
  have hLS : IsAlgebraic ℚ (x : LaurentSeries ℚ) := by
    obtain ⟨P, hP, hPx⟩ := hintQ
    refine IsIntegral.isAlgebraic ⟨P, hP, ?_⟩
    have h := congrArg (algebraMap F (LaurentSeries ℚ)) hPx
    rw [Polynomial.hom_eval₂, map_zero] at h
    convert h using 2 <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _ | exact RingHom.ext_rat _ _
  have hxC := LaurentSeries.eq_C_coeff_zero_of_isAlgebraic hLS
  set c : ℚ := (x : LaurentSeries ℚ).coeff 0 with hc
  have hxc : x = algebraMap ℚ F c := by
    apply Subtype.ext
    rw [hxC]
    change HahnSeries.C c = ((algebraMap ℚ F c : F) : LaurentSeries ℚ)
    rw [HahnSeries.C_eq_algebraMap]
    rfl

  have hcint : IsIntegral ℤℓ c := by
    rw [hxc] at hint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ F).injective).mp hint
  haveI := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p (Fact.out)
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤℓ) (K := ℚ)).mp hcint
  exact ⟨r, by rw [hxc, ← hr]; rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem hconst (x : F) (hx0 : x ∈ chartAlgFin ℤℓ F j) (hx1 : x ∈ chartAlgInf ℤℓ F j) :
    ∃ r : ℤℓ, algebraMap ℤℓ F r = x := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap p Γ j hx0 hx1
  exact ⟨r, by rw [hr]; rfl⟩

end XHChartConstants

end

noncomputable section

p2m_open "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel Polynomial AlgebraicGeometry.Polynomial"

namespace TCIMCechH1Finite

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
  [hft : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j)]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt p)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_finset_span_polynomial :
    ∃ T : Finset F, (↑T ⊆ (chartAlgFin ℤℓ F j : Set F)) ∧ ∀ a : F, a ∈ chartAlgFin ℤℓ F j →
      ∃ f : F → ℤℓ[X], a = ∑ t ∈ T, aeval j (f t) * t := by
  classical
  let P0 : Subalgebra ℤℓ F := Algebra.adjoin ℤℓ {j}
  have hle : P0 ≤ chartAlgFin ℤℓ F j := adjoin_le_chartAlg ℤℓ F _
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤℓ ↥(chartAlgFin ℤℓ F j)).FG)

  let s' : Finset F := s.image Subtype.val
  have hs'sub : (↑s' : Set F) ⊆ chartAlgFin ℤℓ F j := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hs'int : ∀ x ∈ (↑s' : Set F), IsIntegral P0 x := fun x hx =>
    (mem_chartAlg_iff ℤℓ F).mp (hs'sub hx)
  have hFG : (Algebra.adjoin P0 (↑s' : Set F)).toSubmodule.FG :=
    fg_adjoin_of_finite s'.finite_toSet hs'int
  obtain ⟨T, hT⟩ := hFG

  have hadj : (chartAlgFin ℤℓ F j : Subalgebra ℤℓ F) = Algebra.adjoin ℤℓ (↑s' : Set F) := by
    have h1 : (Algebra.adjoin ℤℓ (↑s : Set ↥(chartAlgFin ℤℓ F j))).map (chartAlgFin ℤℓ F j).val =
        Algebra.adjoin ℤℓ (↑s' : Set F) := by
      rw [AlgHom.map_adjoin]
      congr 1
      simp [s']
    rw [← h1, hs, Algebra.map_top, Subalgebra.range_val]

  let A0' : Subalgebra P0 F :=
    { (chartAlgFin ℤℓ F j).toSubring with
      algebraMap_mem' := fun r => hle r.2 }
  have hsub1 : Algebra.adjoin P0 (↑s' : Set F) ≤ A0' := Algebra.adjoin_le hs'sub
  have hsub2 : Algebra.adjoin ℤℓ (↑s' : Set F) ≤ (Algebra.adjoin P0 (↑s' : Set F)).restrictScalars ℤℓ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  refine ⟨T, ?_, fun a ha => ?_⟩
  · intro t ht
    have : (t : F) ∈ (Algebra.adjoin P0 (↑s' : Set F)).toSubmodule := by
      rw [← hT]; exact Submodule.subset_span ht
    exact hsub1 this
  · have ha' : a ∈ Submodule.span P0 (↑T : Set F) := by
      rw [hT]
      have ha2 : a ∈ Algebra.adjoin ℤℓ (↑s' : Set F) := hadj ▸ ha
      exact hsub2 ha2
    obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp ha'
    have hpoly : ∀ t, ∃ f : ℤℓ[X], ((g t : P0) : F) = aeval j f := fun t => by
      have hmem : ((g t : P0) : F) ∈ Algebra.adjoin ℤℓ {j} := (g t).2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
      obtain ⟨f, hf⟩ := hmem
      exact ⟨f, hf.symm⟩
    choose f hf using hpoly
    refine ⟨f, ?_⟩
    rw [← hg]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hf, Subalgebra.smul_def]
    rfl

end TCIMCechH1Finite

namespace TCIMCechH1Finite

set_option synthInstance.maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
  [hft : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j)]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt p)

abbrev J : ↥(chartAlgMid ℤℓ F j) := inclFin ℤℓ F j (jChartFin ℤℓ F j)
abbrev U : ↥(chartAlgMid ℤℓ F j) := inclInf ℤℓ F j (jInvChartInf ℤℓ F j)

theorem J_mul_U : J p F j * U p F j = 1 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf]
  exact mul_inv_cancel₀ ((Fact.out : j ≠ 0))

theorem U_pow_mul_J_pow_of_le {i k : ℕ} (h : i ≤ k) : J p F j ^ i * U p F j ^ k = U p F j ^ (k - i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← mul_assoc, ← mul_pow, J_mul_U, one_pow, one_mul, Nat.add_sub_cancel_left]

theorem U_pow_mul_J_pow_of_lt {i k : ℕ} (h : k < i) : J p F j ^ i * U p F j ^ k = J p F j ^ (i - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show k + d + 1 = (d + 1) + k by ring, pow_add, mul_assoc, ← mul_pow, J_mul_U, one_pow,
    mul_one, Nat.add_sub_cancel]

abbrev W : Submodule ℤℓ ↥(chartAlgMid ℤℓ F j) :=
  LinearMap.range (inclFin ℤℓ F j).toLinearMap ⊔ LinearMap.range (inclInf ℤℓ F j).toLinearMap

theorem inclFin_mem_W (a : ↥(chartAlgFin ℤℓ F j)) : inclFin ℤℓ F j a ∈ W p F j :=
  Submodule.mem_sup_left ⟨a, rfl⟩

theorem inclInf_mem_W (b : ↥(chartAlgInf ℤℓ F j)) : inclInf ℤℓ F j b ∈ W p F j :=
  Submodule.mem_sup_right ⟨b, rfl⟩

theorem exists_mul_J_pow_eq (x : ↥(chartAlgMid ℤℓ F j)) :
    ∃ (a : ↥(chartAlgFin ℤℓ F j)) (k : ℕ), x * J p F j ^ k = inclFin ℤℓ F j a := by
  letI := (inclFin ℤℓ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤℓ F j
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (jChartFin ℤℓ F j)) x
  refine ⟨a, k, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using h

theorem exists_mul_U_pow_eq (x : ↥(chartAlgMid ℤℓ F j)) :
    ∃ (b : ↥(chartAlgInf ℤℓ F j)) (k : ℕ), x * U p F j ^ k = inclInf ℤℓ F j b := by
  letI := (inclInf ℤℓ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf ℤℓ F j
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (jInvChartInf ℤℓ F j)) x
  refine ⟨b, k, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem moduleFinite_quotient :
    Module.Finite ℤℓ (↥(chartAlgMid ℤℓ F j) ⧸ W p F j) := by
  classical
  obtain ⟨T, hTsub, hTspan⟩ := exists_finset_span_polynomial p F j

  let M : F → ↥(chartAlgMid ℤℓ F j) := fun t =>
    if h : t ∈ (chartAlgFin ℤℓ F j : Set F) then inclFin ℤℓ F j ⟨t, h⟩ else 0
  have hMcoe : ∀ t ∈ T, (M t : F) = t := fun t ht => by
    simp only [M, dif_pos (hTsub ht), coe_chartIncl]

  have hd : ∀ t, ∃ (b : ↥(chartAlgInf ℤℓ F j)) (d : ℕ), M t * U p F j ^ d = inclInf ℤℓ F j b :=
    fun t => exists_mul_U_pow_eq p F j (M t)
  choose b d hbd using hd

  let G : Finset ↥(chartAlgMid ℤℓ F j) :=
    T.biUnion fun t => (Finset.range (d t)).image fun s => U p F j ^ s * M t
  have hG : ∀ t ∈ T, ∀ s < d t, U p F j ^ s * M t ∈ Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid ℤℓ F j)) :=
    fun t ht s hs => Submodule.subset_span (Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩⟩)

  have hkey : ∀ x : ↥(chartAlgMid ℤℓ F j), x ∈ W p F j ⊔ Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid ℤℓ F j)) := by
    intro x
    obtain ⟨a, k, hak⟩ := exists_mul_J_pow_eq p F j x
    have hx : x = inclFin ℤℓ F j a * U p F j ^ k := by
      rw [← hak, mul_assoc, ← mul_pow, J_mul_U, one_pow, mul_one]
    obtain ⟨f, hf⟩ := hTspan a a.2
    have ha : inclFin ℤℓ F j a = ∑ t ∈ T, aeval (J p F j) (f t) * M t := by
      apply Subtype.ext
      rw [coe_chartIncl, hf]
      rw [← Subalgebra.coe_val, map_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_mul]
      change _ = ((aeval (J p F j) (f t) : ↥(chartAlgMid ℤℓ F j)) : F) * (M t : F)
      rw [hMcoe t ht, Polynomial.aeval_subalgebra_coe, coe_chartIncl, coe_jChartFin]
    rw [hx, ha, Finset.sum_mul]
    refine Submodule.sum_mem _ fun t ht => ?_
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    rw [mul_right_comm]
    rcases le_or_gt i k with hik | hik
    · rw [U_pow_mul_J_pow_of_le p F j hik]
      rcases lt_or_ge (k - i) (d t) with hlt | hge
      · exact Submodule.mem_sup_right (hG t ht _ hlt)
      · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hge
        refine ⟨jInvChartInf ℤℓ F j ^ e * b t, ?_⟩
        change inclInf ℤℓ F j (jInvChartInf ℤℓ F j ^ e * b t) = _
        rw [he, add_comm, pow_add, mul_assoc, mul_comm (U p F j ^ d t), hbd t, map_mul, map_pow]
    · rw [U_pow_mul_J_pow_of_lt p F j hik]
      refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
      by_cases hmem : (t : F) ∈ (chartAlgFin ℤℓ F j : Set F)
      · refine ⟨jChartFin ℤℓ F j ^ (i - k) * ⟨t, hmem⟩, ?_⟩
        change inclFin ℤℓ F j (jChartFin ℤℓ F j ^ (i - k) * ⟨t, hmem⟩) = _
        rw [map_mul, map_pow]
        simp only [M, dif_pos hmem]
      · refine ⟨0, ?_⟩
        change inclFin ℤℓ F j 0 = _
        simp only [M, dif_neg hmem, mul_zero, map_zero]

  rw [Module.finite_def]
  have htop : (⊤ : Submodule ℤℓ (↥(chartAlgMid ℤℓ F j) ⧸ W p F j)) =
      (Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid ℤℓ F j))).map (W p F j).mkQ := by
    refine le_antisymm ?_ le_top
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (W p F j) y
    obtain ⟨w, hw, g, hg, rfl⟩ := Submodule.mem_sup.mp (hkey x)
    refine ⟨g, hg, ?_⟩
    simp only [map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero (W p F j)).mpr hw, zero_add]
  rw [htop]
  exact (Submodule.fg_span G.finite_toSet).map _

end TCIMCechH1Finite

end

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (L : Type) [Field L] [IsAlgClosed L] [Algebra (R p) L] :
    ConnectedSpace ↥(Limits.pullback (toBase p (ΓM M H) hj) (Scheme.TwoAffineOpenCover.specMap (R p) L)) := by
  haveI : (ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  haveI : Algebra.FiniteType (R p)
      ↥(TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) :=
    (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
      (ModularCurve.translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1
  exact AlgebraicCurve.TwoChartIntegralModel.connectedSpace_pullback_toBase_specMap_ratLocalizedAt p
    ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    (XHChartConstants.hconst p (ΓM M H) (jAt (ΓM M H) hj))
    (TCIMCechH1Finite.moduleFinite_quotient p ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    ⟨𝔛.εinf.1, 𝔛.εinf.2⟩ L

end S_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed (solution)
