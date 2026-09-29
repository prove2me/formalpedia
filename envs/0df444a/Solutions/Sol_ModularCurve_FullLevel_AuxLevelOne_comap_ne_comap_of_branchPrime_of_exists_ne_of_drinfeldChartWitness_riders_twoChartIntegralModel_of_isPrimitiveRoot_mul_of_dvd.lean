-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.comap_ne_comap_of_branchPrime_of_exists_ne_of_drinfeldChartWitness_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6d1b1d5c-df0f-5da1-b0fd-e4be7f1d7904

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_comap_ne_comap_of_branchPrime_of_exists_ne_of_drinfeldChartWitness_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

namespace IGREG

theorem mem_span_X_of_constantCoeff_eq_zero {R : Type} [CommRing R] (h : MvPowerSeries (Fin 2) R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1} := by
  classical
  let h₁ : MvPowerSeries (Fin 2) R := fun m => if m 0 = 0 then h m else 0
  have hc : ∀ (m : Fin 2 →₀ ℕ) (g : MvPowerSeries (Fin 2) R), MvPowerSeries.coeff m g = g m := fun _ _ => rfl
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣ h₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    rw [hc]
    show (if m 0 = 0 then h m else 0) = 0
    split_ifs with hm0
    · have hm : m = 0 := by
        ext i; fin_cases i
        · simpa using hm0
        · simpa using hm1
      subst hm
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
      exact h0
    · rfl
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ∣ (h - h₁) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm0
    rw [map_sub, hc, hc, sub_eq_zero]
    show h m = (if m 0 = 0 then h m else 0)
    rw [if_pos hm0]
  obtain ⟨a, ha⟩ := hX0
  obtain ⟨b, hb⟩ := hX1
  have heq : h = MvPowerSeries.X 0 * a + MvPowerSeries.X 1 * b := by rw [← ha, ← hb, sub_add_cancel]
  rw [heq]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end IGREG

namespace B4Sol

open MvPowerSeries

section LineMove

variable {W : Type} [CommRing W]

local notation "R2" => MvPowerSeries (Fin 2) W

noncomputable abbrev XI (W : Type) [CommRing W] : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}

theorem lineMove (g : R2) (π : W)
    (θ : (R2 ⧸ Ideal.span {g}) ≃+* (R2 ⧸ Ideal.span {g}))
    (hθW : ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {g}) (C w)) = Ideal.Quotient.mk (Ideal.span {g}) (C w))
    (M : Matrix (Fin 2) (Fin 2) W) (c : W) (hc : IsUnit c) (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (hlin : ∀ jj : Fin 2, θ (Ideal.Quotient.mk (Ideal.span {g}) (X jj)) -
        Ideal.Quotient.mk (Ideal.span {g}) (∑ ii : Fin 2, C (M ii jj) * X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) (X 0), Ideal.Quotient.mk (Ideal.span {g}) (X 1)}) ^ 2)
    (hM : ∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ Ideal.span {π})
    (P : Ideal (R2 ⧸ Ideal.span {g})) (hPπ : Ideal.Quotient.mk (Ideal.span {g}) (C π) ∈ P) (a b : ℤ)
    (hab : ∃ h ∈ (XI W) ^ 2,
      Ideal.Quotient.mk (Ideal.span {g}) (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h) ∈ P) :
    ∃ h ∈ (XI W) ^ 2,
      Ideal.Quotient.mk (Ideal.span {g})
        (C (((γ 0 0 * a + γ 0 1 * b : ℤ)) : W) * X 0 + C (((γ 1 0 * a + γ 1 1 * b : ℤ)) : W) * X 1 + h) ∈
        P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) := by
  classical
  set mk : R2 →+* R2 ⧸ Ideal.span {g} := Ideal.Quotient.mk (Ideal.span {g}) with hmk
  set J : Ideal (R2 ⧸ Ideal.span {g}) := Ideal.span {mk (X 0), mk (X 1)} with hJ
  have hJmap : J = (XI W).map mk := by
    rw [hJ, XI, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

  have hθX : ∀ jj : Fin 2, θ (mk (X jj)) ∈ J := by
    intro jj
    have h1 : mk (∑ ii : Fin 2, C (M ii jj) * X ii) ∈ J := by
      rw [map_sum]
      refine Ideal.sum_mem _ (fun ii _ => ?_)
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      fin_cases ii <;> simp
    have h2 : θ (mk (X jj)) - mk (∑ ii : Fin 2, C (M ii jj) * X ii) ∈ J :=
      Ideal.pow_le_self two_ne_zero (hlin jj)
    have := J.add_mem h2 h1
    rwa [sub_add_cancel] at this
  have hθJ : J.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) ≤ J := by
    rw [hJ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hθX 0
    · exact hθX 1
  have hθJ2 : ∀ x ∈ J ^ 2, θ x ∈ J ^ 2 := by
    intro x hx
    have : (J ^ 2).map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) ≤ J ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hθJ 2
    exact this (Ideal.mem_map_of_mem _ hx)
  obtain ⟨h, hh, hmem⟩ := hab
  have hmkh : mk h ∈ J ^ 2 := by
    rw [hJmap, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hh
  have hθint : ∀ z : ℤ, θ (mk (C ((z : ℤ) : W))) = mk (C ((z : ℤ) : W)) := fun z => hθW _
  obtain ⟨r0, hr0, e0⟩ : ∃ r ∈ J ^ 2, θ (mk (X 0)) = mk (∑ ii : Fin 2, C (M ii 0) * X ii) + r :=
    ⟨_, hlin 0, by abel⟩
  obtain ⟨r1, hr1, e1⟩ : ∃ r ∈ J ^ 2, θ (mk (X 1)) = mk (∑ ii : Fin 2, C (M ii 1) * X ii) + r :=
    ⟨_, hlin 1, by abel⟩
  have hMw : ∀ ii jj : Fin 2, ∃ w : W, M ii jj = c * ((γ ii jj : ℤ) : W) + w * π := by
    intro ii jj
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hM ii jj)
    exact ⟨w, by linear_combination -hw⟩
  choose w hw using hMw
  have himg : θ (mk (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h)) ∈
      P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) := Ideal.mem_map_of_mem _ hmem
  set a' : ℤ := γ 0 0 * a + γ 0 1 * b with ha'
  set b' : ℤ := γ 1 0 * a + γ 1 1 * b with hb'
  have hπθ : mk (C π) ∈ P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) := by
    have := Ideal.mem_map_of_mem (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) hPπ
    rwa [RingHom.coe_coe, hθW] at this
  have key : θ (mk (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h)) =
      mk (C c) * (mk (C ((a' : ℤ) : W) * X 0 + C ((b' : ℤ) : W) * X 1)) +
      mk (C π) * mk (C (((a : ℤ) : W) * w 0 0 + ((b : ℤ) : W) * w 0 1) * X 0 +
                      C (((a : ℤ) : W) * w 1 0 + ((b : ℤ) : W) * w 1 1) * X 1) +
      (mk (C ((a : ℤ) : W)) * r0 + mk (C ((b : ℤ) : W)) * r1 + θ (mk h)) := by
    simp only [map_add, map_mul, hθint, e0, e1, Fin.sum_univ_two, hw, ha', hb', Int.cast_add, Int.cast_mul, map_sum,
      map_intCast]
    ring

  have hRr : mk (C ((a : ℤ) : W)) * r0 + mk (C ((b : ℤ) : W)) * r1 + θ (mk h) ∈ J ^ 2 :=
    (J ^ 2).add_mem ((J ^ 2).add_mem (Ideal.mul_mem_left _ _ hr0) (Ideal.mul_mem_left _ _ hr1)) (hθJ2 _ hmkh)
  have h3 : mk (C c) * (mk (C ((a' : ℤ) : W) * X 0 + C ((b' : ℤ) : W) * X 1)) +
      (mk (C ((a : ℤ) : W)) * r0 + mk (C ((b : ℤ) : W)) * r1 + θ (mk h)) ∈
      P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) := by
    rw [key] at himg
    have hsub := (P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g}))).sub_mem himg
      (Ideal.mul_mem_right (mk (C (((a : ℤ) : W) * w 0 0 + ((b : ℤ) : W) * w 0 1) * X 0 +
                      C (((a : ℤ) : W) * w 1 0 + ((b : ℤ) : W) * w 1 1) * X 1)) _ hπθ)
    convert hsub using 1
    ring
  obtain ⟨u, hu⟩ := hc
  have h4 : mk (C ((a' : ℤ) : W) * X 0 + C ((b' : ℤ) : W) * X 1) +
      mk (C ((u⁻¹ : Wˣ) : W)) * (mk (C ((a : ℤ) : W)) * r0 + mk (C ((b : ℤ) : W)) * r1 + θ (mk h)) ∈
      P.map (θ : (R2 ⧸ Ideal.span {g}) →+* (R2 ⧸ Ideal.span {g})) := by
    have hunit : mk (C ((u⁻¹ : Wˣ) : W)) * mk (C c) = 1 := by
      rw [← map_mul, ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
    have := Ideal.mul_mem_left _ (mk (C ((u⁻¹ : Wˣ) : W))) h3
    rwa [mul_add, ← mul_assoc, hunit, one_mul] at this
  have h5 : mk (C ((u⁻¹ : Wˣ) : W)) * (mk (C ((a : ℤ) : W)) * r0 + mk (C ((b : ℤ) : W)) * r1 + θ (mk h)) ∈ J ^ 2 :=
    Ideal.mul_mem_left _ _ hRr
  rw [hJmap, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective] at h5
  obtain ⟨h', hh', hh'eq⟩ := h5
  refine ⟨h', hh', ?_⟩
  rw [map_add, hh'eq]
  exact h4

end LineMove

end B4Sol

namespace B4Sol

theorem twoTrans (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℤ)
    (hv : ¬ (q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) (hw : ¬ (q : ℤ) ∣ c₁ * d₂ - c₂ * d₁) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma ℓ ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      (q : ℤ) ∣ (γ 0 0 * a₁ + γ 0 1 * b₁) * d₁ - c₁ * (γ 1 0 * a₁ + γ 1 1 * b₁) ∧
      (q : ℤ) ∣ (γ 0 0 * a₂ + γ 0 1 * b₂) * d₂ - c₂ * (γ 1 0 * a₂ + γ 1 1 * b₂) := by

  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set Dv : ZMod q := (a₁ : ZMod q) * b₂ - a₂ * b₁ with hDv
  set Dw : ZMod q := (c₁ : ZMod q) * d₂ - c₂ * d₁ with hDw
  have hDv0 : Dv ≠ 0 := by
    intro h; apply hv; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
  have hDw0 : Dw ≠ 0 := by
    intro h; apply hw; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
  set μ : ZMod q := Dv * Dw⁻¹ with hμ

  let Am : Matrix (Fin 2) (Fin 2) (ZMod q) :=
    !![Dv⁻¹ * ((c₁ : ZMod q) * b₂ - μ * c₂ * b₁), Dv⁻¹ * (-(c₁ : ZMod q) * a₂ + μ * c₂ * a₁);
       Dv⁻¹ * ((d₁ : ZMod q) * b₂ - μ * d₂ * b₁), Dv⁻¹ * (-(d₁ : ZMod q) * a₂ + μ * d₂ * a₁)]
  have hdet : Am.det = 1 := by
    simp only [Am, Matrix.det_fin_two_of]
    rw [hμ]
    field_simp
    rw [hDv, hDw]
    ring
  let A : SL(2, ZMod q) := ⟨Am, hdet⟩

  obtain ⟨γ₀, hγ₀, -⟩ := Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime q 1
    (Nat.coprime_one_right q) A 1
  obtain ⟨δ, hδℓ, hδM', -, hδq⟩ :=
    CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd q M' hqM' ℓ hℓq γ₀
  have hmap : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) δ = A := by
    have h1 := CongruenceSubgroup.Gamma_mem'.mp hδq
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.trans hγ₀
  have hent : ∀ i j : Fin 2, ((δ i j : ℤ) : ZMod q) = Am i j := by
    intro i j
    have := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) hmap
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this
  refine ⟨δ, hδℓ, hδM', ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hent, hent, hent, hent]
    simp only [Am, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [hμ]; field_simp; rw [hDv]; ring
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hent, hent, hent, hent]
    simp only [Am, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [hμ]; field_simp; rw [hDv, hDw]; ring

end B4Sol

theorem XiPort.exists_emb (m : ℕ) [NeZero m] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {m} ℚ L] (ξ : L) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι₀ : L →+* ℂ, ι₀ ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite_of_singleton (n := m) ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})

    (hW :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)))

    (hEQ :

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∃ Q₁ Q₂ : Ideal STK, Q₁.IsPrime ∧ Q₂.IsPrime ∧ ϖz ∈ Q₁ ∧ ϖz ∈ Q₂ ∧ ¬ Q₁.IsMaximal ∧ ¬ Q₂.IsMaximal ∧ Q₁ ≠ Q₂) →

      (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

        (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
        (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
              ∈ P₁) →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
              ∈ P₂) →
        ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
          Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) := by

  have hℓq : ℓ ≠ q := fun h => hqM' (h ▸ hℓM')
  have hℓ3 : 3 ≤ ℓ := by omega
  haveI hmne0 : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    obtain ⟨ι₀, h⟩ := XiPort.exists_emb (q * ℓ) L ξ hξ; exact ⟨ι₀, by rw [h]; push_cast; rfl⟩

  have hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by
    obtain ⟨ι, hι'⟩ := hι
    refine ⟨ι, ?_⟩
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    rw [hζξ, map_pow, hι', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp

  intro STK CMP toC S mkS germY
  intro hTwo
  intro a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hX₁ hX₂ hϖP₁ hϖP₂ hlin₁ hlin₂ hdet heq
  classical
  haveI := hP₁
  haveI := hP₂

  let φA : A →+* STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom.comp
      ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  have hφAϖ : φA ϖ = ϖz := by rw [hϖz]; rfl
  have hconst := hW.1
  have heqlin := hW.2
  have hEQfin := hEQ.1
  have hEQfix := hEQ.2
  let ψ : STK →+* S := (e : CMP →+* S).comp toC
  have hψϖ : ψ ϖz = mkS (MvPowerSeries.C (σ ϖ)) := by
    rw [← hφAϖ]; exact hconst ϖ
  let C := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
  let γC : C →+* S := ψ.comp germY

  letI algASTK : Algebra A STK := φA.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ L := by
    haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite {q * ℓ} ℚ L
    infer_instance
  obtain ⟨htj, hFD, hsep⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
      (q ^ 2 * M') H₁ L K hK A j hj
  obtain ⟨hFT, hFT'⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  obtain ⟨hNoeth, -, hDom, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
      A (↥K) hinjAK j hFT hFT' z (fun r => rfl)
  haveI : IsNoetherianRing STK := hNoeth

  have hAq' : (q : A) ∈ Ideal.span {ϖ} := by rw [← hϖ]; exact hAq
  obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.mp hAq'
  have hqW : ((q : ℕ) : W) ∈ IsLocalRing.maximalIdeal W := by
    rw [hσϖ]; refine Ideal.mem_span_singleton'.mpr ⟨σ a0, ?_⟩; rw [← map_mul, ha0, map_natCast]
  have hπ0 : σ ϖ ≠ 0 := by
    intro h0; apply IsDiscreteValuationRing.not_a_field W; rw [hσϖ, h0, Ideal.span_singleton_eq_bot]
  have hcW : σ ϖ ∈ IsLocalRing.maximalIdeal W := by rw [hσϖ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨hBi, hBii, hBiii, -⟩ := DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W (σ ϖ) hσϖ hqW
    (σ ϖ) hcW hπ0 f u v hu hv hf

  have hmaxC : IsLocalRing.maximalIdeal CMP = (IsLocalRing.maximalIdeal STK).map toC :=
    AdicCompletion.maximalIdeal_eq_map
  have hcomap_max : (IsLocalRing.maximalIdeal CMP).comap toC = IsLocalRing.maximalIdeal STK :=
    ((IsLocalRing.maximalIdeal.isMaximal STK).eq_of_le
      (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal CMP).ne_top)
      (by rw [hmaxC]; exact Ideal.le_comap_map)).symm
  obtain ⟨_, hNoethC, -, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing STK (IsLocalRing.maximalIdeal STK)
  haveI : IsNoetherianRing CMP := hNoethC
  haveI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv CMP e
  haveI : Module.FaithfullyFlat STK CMP := by
    refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal STK CMP).mpr ⟨inferInstance, fun I hI htop => ?_⟩
    have hle : I • (⊤ : Submodule STK CMP) ≤ (IsLocalRing.maximalIdeal STK) • ⊤ :=
      Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
    rw [htop, top_le_iff, Ideal.smul_top_eq_map, ← hmaxC] at hle
    have h1 : (1 : CMP) ∈ (IsLocalRing.maximalIdeal CMP).restrictScalars STK := by rw [hle]; trivial
    exact (IsLocalRing.maximalIdeal.isMaximal CMP).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hSmax : ∀ P : Ideal S, P.IsPrime → mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
      mkS (MvPowerSeries.X 0) ∈ P → mkS (MvPowerSeries.X 1) ∈ P → (P.comap ψ).IsMaximal := by
    intro P hP hPπ hP0 hP1
    haveI := hP
    haveI : IsLocalRing S := e.isLocalRing
    have hmS : IsLocalRing.maximalIdeal S ≤ P := by
      intro s hs
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
      have hg : ¬ IsUnit g := fun hu' => (IsLocalRing.mem_maximalIdeal _).mp hs (hu'.map mkS)
      rw [MvPowerSeries.isUnit_iff_constantCoeff] at hg
      have hcc : MvPowerSeries.constantCoeff g ∈ Ideal.span {σ ϖ} := by
        rw [← hσϖ]; exact (IsLocalRing.mem_maximalIdeal _).mpr hg
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hcc
      have hdec : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
        IGREG.mem_span_X_of_constantCoeff_eq_zero _ (by simp)
      have h1 : mkS (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
        have hle : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map mkS ≤ P := by
          rw [Ideal.map_span, Ideal.span_le]
          rintro _ ⟨x, hx, rfl⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          exacts [hP0, hP1]
        exact hle (Ideal.mem_map_of_mem _ hdec)
      have h2 : mkS (MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
        rw [← hw, map_mul, map_mul]; exact Ideal.mul_mem_left _ _ hPπ
      have h12 := P.add_mem h1 h2
      rwa [map_sub, sub_add_cancel] at h12
    have hle : IsLocalRing.maximalIdeal STK ≤ P.comap ψ := by
      intro s hs
      rw [Ideal.mem_comap]
      apply hmS
      show e (toC s) ∈ IsLocalRing.maximalIdeal S
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
      apply Ideal.mem_map_of_mem
      rw [hmaxC]; exact Ideal.mem_map_of_mem _ hs
    have hne : P.comap ψ ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    rw [← (IsLocalRing.maximalIdeal.isMaximal STK).eq_of_le hne hle]
    exact IsLocalRing.maximalIdeal.isMaximal STK

  haveI : IsLocalRing S := e.isLocalRing
  have hmS : ∀ P : Ideal S, mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
      mkS (MvPowerSeries.X 0) ∈ P → mkS (MvPowerSeries.X 1) ∈ P → IsLocalRing.maximalIdeal S ≤ P := by
    intro P hPπ hP0 hP1 s hs
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hg : ¬ IsUnit g := fun hu' => (IsLocalRing.mem_maximalIdeal _).mp hs (hu'.map mkS)
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hg
    have hcc : MvPowerSeries.constantCoeff g ∈ Ideal.span {σ ϖ} := by
      rw [← hσϖ]; exact (IsLocalRing.mem_maximalIdeal _).mpr hg
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hcc
    have hdec : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
      IGREG.mem_span_X_of_constantCoeff_eq_zero _ (by simp)
    have h1 : mkS (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
      have hle : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map mkS ≤ P := by
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨x, hx, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        exacts [hP0, hP1]
      exact hle (Ideal.mem_map_of_mem _ hdec)
    have h2 : mkS (MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
      rw [← hw, map_mul, map_mul]; exact Ideal.mul_mem_left _ _ hPπ
    have h12 := P.add_mem h1 h2
    rwa [map_sub, sub_add_cancel] at h12

  have hcf : MvPowerSeries.constantCoeff f = 0 := by
    have hker : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} ≤
        RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)) := by
      rw [Ideal.span_le]
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, MvPowerSeries.constantCoeff_X]
    have h1 : MvPowerSeries.constantCoeff (f - DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 :=
      hker (Ideal.pow_le_self (by omega) hf)
    have h2 : MvPowerSeries.constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
      have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
      simp [DrinfeldCurve.LocalChart.drinfeldForm, MvPowerSeries.constantCoeff_X, hq0]
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  have hXnu : ∀ i : Fin 2, ¬ IsUnit (mkS (MvPowerSeries.X i)) := by
    intro i hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h1 : mkS (MvPowerSeries.X i * Y - 1) = 0 := by
      rw [map_sub, map_mul, map_one]; exact sub_eq_zero.mpr hy
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨H, hH⟩ := h1
    have h2 := congrArg MvPowerSeries.constantCoeff hH
    simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, hcf,
      zero_mul, mul_zero, sub_zero, zero_sub] at h2

    have hmem : (-1 : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← h2, hσϖ]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by simpa using (IsLocalRing.maximalIdeal W).neg_mem hmem))

  have hSURJ : ∀ Q : Ideal STK, Q.IsPrime → ϖz ∈ Q → ¬ Q.IsMaximal →
      ∃ P : Ideal S, P.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) ∧
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P ∧ P.comap ψ = Q := by
    intro Q hQ hϖQ hQmax
    haveI := hQ
    obtain ⟨P', hP'prime, hP'over⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := STK) (B := CMP) Q
    haveI := hP'prime
    let P : Ideal S := P'.comap (e.symm : S →+* CMP)
    haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ P'
    have hPψ : P.comap ψ = Q := by
      have h1 : P.comap (e : CMP →+* S) = P' := by
        ext x; simp [P]
      show (P.comap (e : CMP →+* S)).comap toC = Q
      rw [h1]; exact hP'over.over.symm
    have hPπ : mkS (MvPowerSeries.C (σ ϖ)) ∈ P := by
      have : ψ ϖz ∈ P := by rw [← Ideal.mem_comap, hPψ]; exact hϖQ
      rwa [hψϖ] at this
    have hPX : mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P := by
      by_contra h
      push Not at h
      exact hQmax (hPψ ▸ hSmax P hPprime hPπ h.1 h.2)
    exact ⟨P, hPprime, hPX, hPπ, hPψ⟩

  obtain ⟨eL, -, heL2⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A (↥K) j z y hy
  let eR := eL.commRingCatIsoToRingEquiv
  have hgermY : ∀ a : C, eR (germY a) = algebraMap C (Localization.AtPrime y.asIdeal) a := fun a => heL2 a
  have hκinj : ∀ Q₁ Q₂ : Ideal STK, Q₁.comap germY = Q₂.comap germY → Q₁ = Q₂ := by
    intro Q₁ Q₂ h
    have hk : ∀ Q : Ideal STK, Q.comap germY =
        (Q.map (eR : STK →+* Localization.AtPrime y.asIdeal)).comap (algebraMap C (Localization.AtPrime y.asIdeal)) := by
      intro Q
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap, ← hgermY]
      constructor
      · intro ha; exact Ideal.mem_map_of_mem _ ha
      · intro ha
        rw [Ideal.mem_map_iff_of_surjective (eR : STK →+* Localization.AtPrime y.asIdeal) eR.surjective] at ha
        obtain ⟨x, hx, hxe⟩ := ha
        exact (eR.injective hxe) ▸ hx
    rw [hk, hk] at h
    have h2 := (IsLocalization.orderEmbedding y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)).injective h
    have h3 := congrArg (Ideal.comap (eR : STK →+* Localization.AtPrime y.asIdeal)) h2
    rwa [Ideal.comap_map_of_bijective (eR : STK →+* Localization.AtPrime y.asIdeal) eR.bijective,
      Ideal.comap_map_of_bijective (eR : STK →+* Localization.AtPrime y.asIdeal) eR.bijective] at h3

  obtain ⟨G, -, hG⟩ := ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
    q M' hqM' ℓ hℓM' L ζ hζ hιζ H₁ hH₁ K hK
  have hτex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ H₁ hH₁ K hK

  have hdetγ : ∀ (γ : SL(2, ℤ)) (x₁ y₁ x₂ y₂ : ℤ),
      (γ 0 0 * x₁ + γ 0 1 * y₁) * (γ 1 0 * x₂ + γ 1 1 * y₂) - (γ 0 0 * x₂ + γ 0 1 * y₂) * (γ 1 0 * x₁ + γ 1 1 * y₁)
        = x₁ * y₂ - x₂ * y₁ := by
    intro γ x₁ y₁ x₂ y₂
    have hd : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ; rwa [Matrix.det_fin_two] at this
    linear_combination (x₁ * y₂ - x₂ * y₁) * hd
  have hall : ∀ (c₁ d₁ c₂ d₂ : ℤ) (R₁ R₂ : Ideal S), R₁.IsPrime → R₂.IsPrime →
      (mkS (MvPowerSeries.X 0) ∉ R₁ ∨ mkS (MvPowerSeries.X 1) ∉ R₁) →
      (mkS (MvPowerSeries.X 0) ∉ R₂ ∨ mkS (MvPowerSeries.X 1) ∉ R₂) →
      mkS (MvPowerSeries.C (σ ϖ)) ∈ R₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ R₂ →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((c₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((d₁ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ R₁) →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((c₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((d₂ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ R₂) →
      ¬ ((q : ℤ) ∣ c₁ * d₂ - c₂ * d₁) → R₁.comap ψ = R₂.comap ψ := by
    intro c₁ d₁ c₂ d₂ R₁ R₂ hR₁ hR₂ hRX₁ hRX₂ hRπ₁ hRπ₂ hRlin₁ hRlin₂ hRdet

    obtain ⟨γ, hγℓ, hγM', hpar₁, hpar₂⟩ := B4Sol.twoTrans q M' hqM' ℓ hℓq a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ hdet hRdet

    obtain ⟨τ, hτ⟩ := hτex γ hγM'
    have hpres := hEQfin γ hγM' τ hτ
    have hfix := hEQfix γ hγM' (CongruenceSubgroup.Gamma_mem.mp hγℓ).2.2.2 τ hτ hpres
    obtain ⟨θ, c, M, hcompat, hWlin, hlinM, hcq, hMγ, -, -⟩ := heqlin γ hγM' τ hτ hpres hfix

    have hτG : τ ∈ G := (hG τ).mpr ⟨γ, hγM', hτ⟩
    obtain ⟨γ', hγ'M', hτ'⟩ := (hG τ⁻¹).mp (G.inv_mem hτG)
    have hpres' := hEQfin γ' hγ'M' τ⁻¹ hτ'
    let τr : C →+* C := (τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres
    have hτr : ∀ a : C, ((τr a : C) : ↥K) = τ (a : ↥K) := fun a => rfl
    have hτrsurj : Function.Surjective τr := by
      intro b
      refine ⟨⟨τ⁻¹ (b : ↥K), hpres' _ b.2⟩, ?_⟩
      apply Subtype.ext
      rw [hτr]
      show τ (τ⁻¹ (b : ↥K)) = b
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

    have hcompat' : ∀ a : C, θ (γC a) = γC (τr a) := fun a => hcompat a

    have hequiv : ∀ Pa : Ideal S, (Pa.map (θ : S →+* S)).comap γC = (Pa.comap γC).map τr := by
      intro Pa
      ext a
      rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective τr hτrsurj]
      constructor
      · intro ha
        obtain ⟨a₀, rfl⟩ := hτrsurj a
        refine ⟨a₀, ?_, rfl⟩
        rw [Ideal.mem_comap]
        rw [← hcompat'] at ha
        rw [Ideal.mem_map_iff_of_surjective (θ : S →+* S) θ.surjective] at ha
        obtain ⟨x, hx, hxe⟩ := ha
        exact (θ.injective hxe) ▸ hx
      · rintro ⟨a₀, ha₀, rfl⟩
        rw [← hcompat']
        exact Ideal.mem_map_of_mem _ ha₀

    have hcunit : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hcu
      have : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
        have h1 := Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal W) hcm (q + 1) (Nat.succ_pos q)
        have h2 := (IsLocalRing.maximalIdeal W).sub_mem h1 hcq
        rwa [sub_sub_cancel] at h2
      exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hMγ' : ∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ Ideal.span {σ ϖ} := by
      intro ii jj; rw [← hσϖ]; exact hMγ ii jj

    have hθπ : ∀ Pa : Ideal S, mkS (MvPowerSeries.C (σ ϖ)) ∈ Pa →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ Pa.map (θ : S →+* S) := by
      intro Pa h
      have := Ideal.mem_map_of_mem (θ : S →+* S) h
      rwa [RingHom.coe_coe, hWlin] at this
    have hθprime : ∀ Pa : Ideal S, Pa.IsPrime → (Pa.map (θ : S →+* S)).IsPrime := by
      intro Pa hPa
      haveI := hPa
      exact Ideal.map_isPrime_of_equiv θ
    have hθX : ∀ Pa : Ideal S, Pa.IsPrime → (mkS (MvPowerSeries.X 0) ∉ Pa ∨ mkS (MvPowerSeries.X 1) ∉ Pa) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ Pa →
        (mkS (MvPowerSeries.X 0) ∉ Pa.map (θ : S →+* S) ∨ mkS (MvPowerSeries.X 1) ∉ Pa.map (θ : S →+* S)) := by
      intro Pa hPa hPaX hPaπ
      by_contra h
      push Not at h
      have hle := hmS _ (hθπ Pa hPaπ) h.1 h.2
      have hne : Pa.map (θ : S →+* S) ≠ ⊤ := (hθprime Pa hPa).ne_top
      have heqm : Pa.map (θ : S →+* S) = IsLocalRing.maximalIdeal S :=
        ((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le hne hle).symm
      have hPa_eq : Pa = IsLocalRing.maximalIdeal S := by
        have h1 := congrArg (Ideal.comap (θ : S →+* S)) heqm
        rw [Ideal.comap_map_of_bijective (θ : S →+* S) θ.bijective] at h1
        rw [h1]
        ext x
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          mem_nonunits_iff, RingHom.coe_coe]
        exact (isUnit_map_iff θ x).not
      rw [hPa_eq] at hPaX
      rcases hPaX with h0 | h1'
      · exact h0 ((IsLocalRing.mem_maximalIdeal _).mpr (hXnu 0))
      · exact h1' ((IsLocalRing.mem_maximalIdeal _).mpr (hXnu 1))

    obtain ⟨k₁, hk₁, hk₁mem⟩ := B4Sol.lineMove (MvPowerSeries.C (σ ϖ) * v - f * u) (σ ϖ) θ hWlin M c hcunit
      (γ : Matrix (Fin 2) (Fin 2) ℤ) hlinM hMγ' P₁ hϖP₁ a₁ b₁ hlin₁
    obtain ⟨k₂, hk₂, hk₂mem⟩ := B4Sol.lineMove (MvPowerSeries.C (σ ϖ) * v - f * u) (σ ϖ) θ hWlin M c hcunit
      (γ : Matrix (Fin 2) (Fin 2) ℤ) hlinM hMγ' P₂ hϖP₂ a₂ b₂ hlin₂
    have hndR₁ : ¬ ((q : ℤ) ∣ c₁ ∧ (q : ℤ) ∣ d₁) := fun h =>
      hRdet (dvd_sub (Dvd.dvd.mul_right h.1 d₂) (Dvd.dvd.mul_left h.2 c₂))
    have hndR₂ : ¬ ((q : ℤ) ∣ c₂ ∧ (q : ℤ) ∣ d₂) := fun h =>
      hRdet (dvd_sub (Dvd.dvd.mul_left h.2 c₁) (Dvd.dvd.mul_right h.1 d₁))
    have hdet' : ¬ (q : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * a₁ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * b₁) *
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * a₂ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b₂) -
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * a₂ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * b₂) *
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * a₁ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b₁) := by
      rw [hdetγ]; exact hdet
    have hnd₁' : ¬ ((q : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * a₁ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * b₁) ∧
        (q : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * a₁ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b₁)) := fun h =>
      hdet' (dvd_sub (Dvd.dvd.mul_right h.1 _) (Dvd.dvd.mul_left h.2 _))
    have hnd₂' : ¬ ((q : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * a₂ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * b₂) ∧
        (q : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * a₂ + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * b₂)) := fun h =>
      hdet' (dvd_sub (Dvd.dvd.mul_left h.2 _) (Dvd.dvd.mul_right h.1 _))
    have hθP₁ : P₁.map (θ : S →+* S) = R₁ :=
      (hBiii _ _ c₁ d₁ (P₁.map (θ : S →+* S)) R₁ (hθprime P₁ hP₁) hR₁ (hθX P₁ hP₁ hX₁ hϖP₁) hRX₁
        (hθπ P₁ hϖP₁) hRπ₁ ⟨k₁, hk₁, hk₁mem⟩ hRlin₁ hnd₁' hndR₁).mpr hpar₁
    have hθP₂ : P₂.map (θ : S →+* S) = R₂ :=
      (hBiii _ _ c₂ d₂ (P₂.map (θ : S →+* S)) R₂ (hθprime P₂ hP₂) hR₂ (hθX P₂ hP₂ hX₂ hϖP₂) hRX₂
        (hθπ P₂ hϖP₂) hRπ₂ ⟨k₂, hk₂, hk₂mem⟩ hRlin₂ hnd₂' hndR₂).mpr hpar₂

    apply hκinj
    rw [Ideal.comap_comap, Ideal.comap_comap, ← hθP₁, ← hθP₂]
    show (P₁.map (θ : S →+* S)).comap γC = (P₂.map (θ : S →+* S)).comap γC
    have hγCeq : P₁.comap γC = P₂.comap γC := by
      show P₁.comap (ψ.comp germY) = P₂.comap (ψ.comp germY)
      rw [← Ideal.comap_comap, ← Ideal.comap_comap]
      show (P₁.comap ((e : CMP →+* S).comp toC)).comap germY = (P₂.comap ((e : CMP →+* S).comp toC)).comap germY
      rw [heq]
    rw [hequiv, hequiv, hγCeq]

  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hϖQ₁, hϖQ₂, hQ₁m, hQ₂m, hQne⟩ := hTwo
  obtain ⟨R₁, hR₁, hRX₁, hRπ₁, hRQ₁⟩ := hSURJ Q₁ hQ₁ hϖQ₁ hQ₁m
  obtain ⟨R₂, hR₂, hRX₂, hRπ₂, hRQ₂⟩ := hSURJ Q₂ hQ₂ hϖQ₂ hQ₂m
  obtain ⟨c₁, d₁, hndR₁, hRlin₁⟩ := hBii R₁ hR₁ hRX₁ hRπ₁
  obtain ⟨c₂, d₂, hndR₂, hRlin₂⟩ := hBii R₂ hR₂ hRX₂ hRπ₂
  apply hQne
  rw [← hRQ₁, ← hRQ₂]
  by_cases hRdet : (q : ℤ) ∣ c₁ * d₂ - c₂ * d₁
  · rw [(hBiii c₁ d₁ c₂ d₂ R₁ R₂ hR₁ hR₂ hRX₁ hRX₂ hRπ₁ hRπ₂ hRlin₁ hRlin₂ hndR₁ hndR₂).mpr hRdet]
  · exact hall c₁ d₁ c₂ d₂ R₁ R₂ hR₁ hR₂ hRX₁ hRX₂ hRπ₁ hRπ₂ hRlin₁ hRlin₂ hRdet

end S_ModularCurve_FullLevel_AuxLevelOne_comap_ne_comap_of_branchPrime_of_exists_ne_of_drinfeldChartWitness_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_comap_ne_comap_of_branchPrime_of_exists_ne_of_drinfeldChartWitness_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd (solution)
