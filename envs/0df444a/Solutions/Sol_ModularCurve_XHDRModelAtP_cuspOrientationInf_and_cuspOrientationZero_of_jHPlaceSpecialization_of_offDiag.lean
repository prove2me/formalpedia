-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f163f07e-e050-5954-8434-b1166071ed6d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isInftySide_of_section_comp_one
import Theorems.Thm_ModularCurve_XHDRModelAtP_isInftySide_of_isCuspidal_of_section_comp_zero
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag
p2m_attr_erase "instance" "ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

noncomputable section

namespace Readings3

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · rw [hf0, Place.ord_zero]
  by_contra hneg
  push Not at hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ

  have hπ0 : ((π : v.toValuationSubring) : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hzmem : ((π : v.toValuationSubring) : F) ^ (v.ord f) ∈ v.toValuationSubring := by
    have hinv : ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)) : F) *
        (((u : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one]
    have : ((π : v.toValuationSubring) : F) ^ (v.ord f) =
        ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)) : F) * f := by
      conv_rhs => rw [hu]
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (SetLike.coe_mem _) hf

  set n : ℤ := v.ord f with hn
  have hprod : ((π : v.toValuationSubring) : F) ^ n * ((π : v.toValuationSubring) : F) ^ (-n) = 1 := by
    rw [← zpow_add₀ hπ0, add_neg_cancel, zpow_zero]
  have hnat : ((π : v.toValuationSubring) : F) ^ (-n) = (((π ^ (-n).toNat : v.toValuationSubring)) : F) := by
    rw [SubmonoidClass.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  have hunit : IsUnit (π ^ (-n).toNat : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hzmem⟩, Subtype.ext ?_⟩
    show (((π ^ (-n).toNat : v.toValuationSubring)) : F) * ((π : v.toValuationSubring) : F) ^ n = 1
    rw [← hnat, mul_comm, hprod]
  have hk : 1 ≤ (-n).toNat := by omega
  obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le hk
  rw [hk', pow_add, pow_one] at hunit
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left hunit)

end Readings3

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut Place Place.ord_zero Place.HasValue Place.hasValue_one Place.hasValue_algebraMap Place.exists_hasValue_of_surjective Place.deg_eq_one_iff_surjective_algebraMap_residueField Place.ord_add_eq_of_lt"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_zpow exists_unit_mul_zpow toValuationSubring HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ord_nonneg_of_mem deg_eq_one_iff_surjective_algebraMap_residueField ord_add_eq_of_lt"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_ord_nonneg' {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

variable {v}

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mem residue_eq mul ne_zero ord_eq_zero" end HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.sub' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using Place.hasValue_one v
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

theorem HasValue.ord_pos_of_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have hnn := Readings3.ord_nonneg_of_mem v h.mem
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have hres := h.residue_eq
    rw [map_zero] at hres
    have h' : IsLocalRing.residue _ (⟨g, hm⟩ : v.toValuationSubring) ≠ 0 := by
      rw [IsLocalRing.residue_ne_zero_iff_isUnit]; exact hu
    exact h' hres

end AlgebraicCurve.Place

namespace OrientXHDR

set_option maxHeartbeats 1600000 in
theorem isCuspidal_of_isZeroSide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hZ : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hC', x, x', hx, hx', τ, hτ, hval⟩ := hZ
  intro y hy a
  have hyx : y = x := Subtype.ext (by rw [hy, hx])
  rw [hyx]

  have hτ0 : ((τ : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have : τ = 0 := Subtype.ext h0
    rw [this, map_zero] at hτ
    exact zero_ne_one hτ
  have hu0 : x / x' ^ p ≠ 0 := hval.ne_zero hτ0
  have hx'p0 : x' ^ p ≠ 0 := by
    intro h0; apply hu0; rw [h0, div_zero]
  have hx'0 : x' ≠ 0 := fun h0 => hx'p0 (by rw [h0, zero_pow (NeZero.ne p)])
  have hx0 : x ≠ 0 := by
    intro h0; apply hu0; rw [h0, zero_div]
  have hordu : C.ord (x / x' ^ p) = 0 := hval.ord_eq_zero hτ0
  have hxeq : x = x / x' ^ p * x' ^ p := (div_mul_cancel₀ x hx'p0).symm
  have hordx : C.ord x = (p : ℤ) * C.ord x' := by
    conv_lhs => rw [hxeq]
    rw [C.ord_mul hu0 hx'p0, hordu, zero_add, ← zpow_natCast, C.ord_zpow]

  have hconst : ∀ c : AlgebraicClosure ℚ, c ≠ 0 → C.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c) = 0 :=
    fun c hc => (Place.hasValue_algebraMap C c).ord_eq_zero hc
  by_cases hneg : C.ord x' < 0
  ·
    have hxneg : C.ord x < 0 := by
      rw [hordx]
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      nlinarith
    by_cases ha : ((a : ↥A) : AlgebraicClosure ℚ) = 0
    · rw [ha, map_zero, sub_zero]; exact hxneg.le
    · have hca : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (-(a : AlgebraicClosure ℚ)) ≠ 0 := by
        rw [map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).injective]
        exact neg_ne_zero.mpr ha
      have h1 : x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) = x + algebraMap (AlgebraicClosure ℚ) _ (-(a : AlgebraicClosure ℚ)) := by
        rw [map_neg, sub_eq_add_neg]
      rw [h1, Place.ord_add_eq_of_lt C hx0 hca (by rw [hconst _ (neg_ne_zero.mpr ha)]; exact hxneg)]
      exact hxneg.le
  ·
    push Not at hneg
    have hmem' : x' ∈ C.toValuationSubring := Place.mem_of_ord_nonneg' C hx'0 hneg

    haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
    have hdeg : C.deg = 1 := place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
      (translation_mem_GammaH M H) (xHFunctionField M H) rfl C
    have hsurj := (Place.deg_eq_one_iff_surjective_algebraMap_residueField C).mp hdeg
    obtain ⟨c, hc, -⟩ := Place.exists_hasValue_of_surjective C hsurj hmem'
    by_cases hcA : ∃ b : ↥A, (b : AlgebraicClosure ℚ) = c
    ·
      exfalso
      obtain ⟨b, hb⟩ := hcA
      have hval0 : C.HasValue (x' - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) 0 := by
        rw [hb]
        have := Place.HasValue.sub' hc (Place.hasValue_algebraMap C c)
        rwa [sub_self] at this
      have hne : x' - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        have h1 : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
          rw [sub_eq_zero.mp h0]
        have h2 : ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
            = HahnSeries.single 0 ((b : AlgebraicClosure ℚ)) := by
          rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
              = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) from rfl]
          exact algebraMap_laurentSeries_eq_single _ _
        rw [hx', h2] at h1
        have h3 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff ((p : ℤ) * (-1))) h1
        simp only [qExpand_coeff_mul, coeff_jqModC_neg_one] at h3
        rw [HahnSeries.coeff_single_of_ne] at h3
        · exact one_ne_zero h3
        · have : (p : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
          omega
      have hpos := Place.HasValue.ord_pos_of_zero hval0 hne
      have hle := hC' x' hx' b
      omega
    ·
      push Not at hcA
      have hvalx : C.HasValue x ((τ : AlgebraicClosure ℚ) * c ^ p) := by
        have := hval.mul (Place.HasValue.pow' hc p)
        rwa [div_mul_cancel₀ x hx'p0] at this
      have hd : (τ : AlgebraicClosure ℚ) * c ^ p - (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0

        have hτu : IsUnit τ := by
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hτ]; exact one_ne_zero
        obtain ⟨w, hw⟩ := hτu
        have h1 : ((τ : ↥A) : AlgebraicClosure ℚ) * c ^ p = (a : AlgebraicClosure ℚ) := sub_eq_zero.mp h0
        have h2 : (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * ((τ : ↥A) : AlgebraicClosure ℚ) = 1 := by
          rw [← hw, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
        have hcp : c ^ p = (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) := by
          calc c ^ p = ((((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * ((τ : ↥A) : AlgebraicClosure ℚ)) * c ^ p := by
                rw [h2, one_mul]
            _ = (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (((τ : ↥A) : AlgebraicClosure ℚ) * c ^ p) := by ring
            _ = _ := by rw [h1]
        have hcpA : c ^ p ∈ A := by
          rw [hcp]; exact mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _)
        have hint : IsIntegral ↥A (c ^ p) := by
          have : c ^ p = algebraMap ↥A (AlgebraicClosure ℚ) ⟨c ^ p, hcpA⟩ := rfl
          rw [this]; exact isIntegral_algebraMap
        have hint' : IsIntegral ↥A c := IsIntegral.of_pow (Fact.out : p.Prime).pos hint
        obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint'
        exact hcA b hb
      have := (Place.HasValue.sub' hvalx (Place.hasValue_algebraMap C (a : AlgebraicClosure ℚ))).ord_eq_zero hd
      rw [this]

end OrientXHDR

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

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
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
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)) := by
  classical

  have key : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (i : Fin 2),
        𝔛.Meta.pointEquivPlace y = C ∧
        ((i = 0 →
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceFst α hα C))) ∧
         (i = 1 →
          Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)) ∧
         (i = 1 → ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C) ∧
         (i = 0 → JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C →
            JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C)) := by
    intro C
    set y := 𝔛.Meta.pointEquivPlace.symm C with hy
    have hyC : 𝔛.Meta.pointEquivPlace y = C := Equiv.apply_symm_apply _ _
    obtain ⟨u, hu, uκ, huκ₁, huκ₂, i, P0, hP0⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
        p M H hpM hj 𝔛 A hA ρ hρ y
    refine ⟨y, i, hyC, ?_, ?_, ?_, ?_⟩
    · intro hi; subst hi
      have h1 := hcompat 0 y u hu uκ huκ₁ huκ₂ P0 hP0
      have h2 := hcompat' 0 y u hu uκ huκ₁ huκ₂ P0 hP0
      simp only [↓reduceIte] at h1 h2
      rw [hyC] at h1 h2
      rw [h2, h1]
    · intro hi; subst hi
      have h1 := hcompat 1 y u hu uκ huκ₁ huκ₂ P0 hP0
      have h2 := hcompat' 1 y u hu uκ huκ₁ huκ₂ P0 hP0
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte] at h1 h2
      rw [hyC] at h1 h2
      rw [h2, h1]
    · intro hi; subst hi
      rw [← hyC]
      exact ModularCurve.XHDRModelAtP.not_isInftySide_of_section_comp_one p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ y u hu uκ huκ₁ huκ₂ P0 hP0
    · intro hi hc; subst hi
      rw [← hyC] at hc ⊢
      exact ModularCurve.XHDRModelAtP.isInftySide_of_isCuspidal_of_section_comp_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ y u hu uκ huκ₁ huκ₂ P0 hP0 hc
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · obtain ⟨y, i, hyC, h0, h1, hinf, hcusp0⟩ := key C
    fin_cases i
    · exact ((h0 rfl)).symm
    · exact absurd hC (hinf rfl)
  · obtain ⟨y, i, hyC, h0, h1, hinf, hcusp0⟩ := key C
    fin_cases i
    · exact absurd (hcusp0 rfl (OrientXHDR.isCuspidal_of_isZeroSide p M H A C hC))
        (ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA C hC)
    · exact h1 rfl

#print axioms solution

end
end S_ModularCurve_XHDRModelAtP_cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag (solution)
