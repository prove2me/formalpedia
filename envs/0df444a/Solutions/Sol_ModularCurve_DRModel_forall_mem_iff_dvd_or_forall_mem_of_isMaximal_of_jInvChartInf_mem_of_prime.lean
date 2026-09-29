-- Prove2me | solution 1 for ModularCurve.DRModel.forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5d7b37f1-eaa0-5b27-87e4-fd5df7f2b276

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve"

set_option quotPrecheck false in
local notation "Fn" n => (↥(modularFunctionFieldFull n) : Type)

def Pkg (p : ℕ) [Fact p.Prime] (n : ℕ) [NeZero n] : Prop :=
  ∀ (jp' : Fn n), ((jp' : LaurentSeries ℚ) = qExpand ℚ p jq) →
  ∃ W₀ W₁ : ValuationSubring (Fn n),
    W₀ ≠ W₁ ∧
    (∀ i : Fin 2, ((p : ℕ) : Fn n) ∈ (![W₀, W₁] i).nonunits ∧
      (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ (Fn n)) (IgusaScheme.jFull n : Fn n) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ (Fn n)) (IgusaScheme.jFull n : Fn n) P)⁻¹ ∈ (![W₀, W₁] i)) ∧
      (∀ f ∈ (![W₀, W₁] i).nonunits, f * ((p : ℕ) : Fn n)⁻¹ ∈ (![W₀, W₁] i))) ∧
    (∀ V : ValuationSubring (Fn n),
        ((p : ℕ) : Fn n) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ (Fn n)) (IgusaScheme.jFull n : Fn n) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ (Fn n)) (IgusaScheme.jFull n : Fn n) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) ∧
    (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ (Fn n)) (IgusaScheme.jFull n : Fn n)⁻¹)
          (jp' * ((IgusaScheme.jFull n : Fn n)⁻¹) ^ p) = 0) ∧
    (jp' * ((IgusaScheme.jFull n : Fn n)⁻¹) ^ p - 1 ∈ W₀.nonunits) ∧
    ((jp' * ((IgusaScheme.jFull n : Fn n)⁻¹) ^ p) ^ p - ((IgusaScheme.jFull n : Fn n)⁻¹) ^ (p ^ 2 - 1)
        ∈ W₁.nonunits) ∧
    ((((jp' * ((IgusaScheme.jFull n : Fn n)⁻¹) ^ p) ^ p
        - ((IgusaScheme.jFull n : Fn n)⁻¹) ^ (p ^ 2 - 1) : Fn n) : LaurentSeries ℚ).coeff 0 = 1)

theorem Pkg.transport {p : ℕ} [Fact p.Prime] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (H : Pkg p n) : Pkg p m := by
  subst h
  exact H

theorem pkg_one_mul (p : ℕ) [Fact p.Prime] : Pkg p (1 * p) := by
  intro jp' hjp'
  have hnd : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  obtain ⟨W, hW0, hW1, hne, hloc, hcomp⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd 1 p hnd
  obtain ⟨-, ⟨-, ⟨h, hmonic, -, heval⟩, -, -⟩, hopp⟩ :=
    ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd 1 p hnd
  obtain ⟨⟨ht1, -⟩, hs, hscoeff⟩ := hopp (W 0) (W 1) hW0 hW1

  obtain rfl : jp' = ⟨qExpand ℚ p jq, jqd_mem_full (1 * p) (dvd_mul_left p 1)⟩ := Subtype.ext hjp'
  refine ⟨W 0, W 1, hne, ?_, hcomp, ⟨h, hmonic, heval⟩, ht1, hs, hscoeff⟩
  intro i
  fin_cases i
  · exact hloc 0
  · exact hloc 1

theorem pkg (p : ℕ) [Fact p.Prime] [NeZero p] : Pkg p p :=
  Pkg.transport (one_mul p) (pkg_one_mul p)

end ModularCurve.DRModel.C4

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve"

section ValuationLemmas

variable {F : Type} [Field F] (W : ValuationSubring F)

theorem sub_mem_nonunits {x y : F} (hx : x ∈ W.nonunits) (hy : y ∈ W.nonunits) :
    x - y ∈ W.nonunits := by
  obtain ⟨hxW, hx'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  obtain ⟨hyW, hy'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨sub_mem hxW hyW, Ideal.sub_mem _ hx' hy'⟩

theorem mul_mem_nonunits_of_mem {a x : F} (ha : a ∈ W) (hx : x ∈ W.nonunits) :
    a * x ∈ W.nonunits := by
  obtain ⟨hxW, hx'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨mul_mem ha hxW, Ideal.mul_mem_left _ ⟨a, ha⟩ hx'⟩

theorem mem_of_mem_nonunits {x : F} (hx : x ∈ W.nonunits) : x ∈ W :=
  (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx).1

theorem not_mem_nonunits_of_inv_mem {x : F} (hx0 : x ≠ 0) (hinv : x⁻¹ ∈ W) : x ∉ W.nonunits := by
  intro hx
  rw [ValuationSubring.mem_nonunits_iff] at hx
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀,
    inv_le_one₀ ((Valuation.ne_zero_iff _).mpr hx0 |> fun h => lt_of_le_of_ne zero_le' (Ne.symm h))] at hinv
  exact absurd (lt_of_le_of_lt hinv hx) (lt_irrefl _)

theorem pow_sub_one_mem_nonunits {t : F} (ht : t - 1 ∈ W.nonunits) (n : ℕ) : t ^ n - 1 ∈ W.nonunits := by
  obtain ⟨htW, ht'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ht
  have htmem : t ∈ W := by simpa using add_mem htW (one_mem W)
  have hdvd : (⟨t, htmem⟩ - 1 : W) ∣ (⟨t, htmem⟩ ^ n - 1 ^ n) := sub_dvd_pow_sub_pow _ _ n
  rw [one_pow] at hdvd
  have hmem : (⟨t, htmem⟩ ^ n - 1 : W) ∈ IsLocalRing.maximalIdeal W :=
    Ideal.mem_of_dvd _ hdvd (by convert ht' using 1 <;> first | rfl | (apply Subtype.ext; simp) | skip)
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨?_, ?_⟩
  · exact sub_mem (pow_mem htmem n) (one_mem W)
  · convert hmem using 1 <;> first | rfl | (apply Subtype.ext; simp) | skip

theorem not_mem_nonunits_witness (p : ℕ) [Fact p.Prime] (j : F) (hj0 : j ≠ 0)
    (hj1 : j ^ (p ^ 2 - 1) - 1 ≠ 0)
    (hgenW : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) j P ∈ W ∧ (Polynomial.eval₂ (algebraMap ℤ F) j P)⁻¹ ∈ W)
    (t : F) (ht1 : t - 1 ∈ W.nonunits) :
    t ^ p - (j⁻¹) ^ (p ^ 2 - 1) ∉ W.nonunits := by
  have hprime : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hprime.one_lt⟩
  have hk : p ^ 2 - 1 ≠ 0 := by
    have h2 : 2 ≤ p := hprime.two_le
    have : 2 * 2 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h2 h2
    omega

  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  obtain ⟨hjW, hjinvW⟩ := hgenW Polynomial.X hX
  rw [Polynomial.eval₂_X] at hjW hjinvW

  set P : Polynomial ℤ := Polynomial.X ^ (p ^ 2 - 1) - 1 with hP
  have hPbar : P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q => Polynomial.coeff Q (p ^ 2 - 1)) h0
    simp only [hP, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_true, Polynomial.coeff_one, hk,
      if_false, sub_zero, Polynomial.coeff_zero] at hc
    exact one_ne_zero hc
  obtain ⟨hPW, hPinvW⟩ := hgenW P hPbar
  have hPeval : Polynomial.eval₂ (algebraMap ℤ F) j P = j ^ (p ^ 2 - 1) - 1 := by
    simp [hP, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [hPeval] at hPW hPinvW

  set u : F := j⁻¹ with hu
  have huj : u * j = 1 := inv_mul_cancel₀ hj0
  have hy : u ^ (p ^ 2 - 1) * (j ^ (p ^ 2 - 1) - 1) = 1 - u ^ (p ^ 2 - 1) := by
    rw [mul_sub, ← mul_pow, huj, one_pow, mul_one]
  have hyW : 1 - u ^ (p ^ 2 - 1) ∈ W := by rw [← hy]; exact mul_mem (pow_mem hjinvW _) hPW
  have hyinv : (1 - u ^ (p ^ 2 - 1))⁻¹ ∈ W := by
    rw [← hy, mul_inv, ← inv_pow, hu, inv_inv]
    exact mul_mem (pow_mem hjW _) hPinvW
  have hy0 : 1 - u ^ (p ^ 2 - 1) ≠ 0 := by
    rw [← hy]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hj0)) hj1
  have hyunit := not_mem_nonunits_of_inv_mem W hy0 hyinv

  intro hs
  apply hyunit
  have h1 : u ^ (p ^ 2 - 1) - 1 ∈ W.nonunits := by
    have := sub_mem_nonunits W (pow_sub_one_mem_nonunits W ht1 p) hs
    convert this using 1; ring
  have h2 : 1 - u ^ (p ^ 2 - 1) = -1 * (u ^ (p ^ 2 - 1) - 1) := by ring
  rw [h2]
  exact mul_mem_nonunits_of_mem W (neg_mem (one_mem W)) h1

end ValuationLemmas

end ModularCurve.DRModel.C4

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve"

section LevelP

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull p) : Type)
set_option quotPrecheck false in
local notation "J" => (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))

theorem jFull_pow_sub_one_ne_zero :
    (IgusaScheme.jFull p : F) ^ (p ^ 2 - 1) - 1 ≠ 0 := by
  have hprime : p.Prime := Fact.out
  have hk : p ^ 2 - 1 ≠ 0 := by
    have h2 : 2 ≤ p := hprime.two_le
    have : 2 * 2 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h2 h2
    omega
  intro h
  apply ModularCurve.transcendental_jq
  have hcoe := congrArg (fun z : F => (z : LaurentSeries ℚ)) h
  simp only [AddSubgroupClass.coe_sub, IntermediateField.coe_pow, IntermediateField.coe_one,
    IgusaScheme.coe_jFull, ZeroMemClass.coe_zero] at hcoe
  refine ⟨Polynomial.X ^ (p ^ 2 - 1) - 1, ?_, ?_⟩
  · have := Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : ℚ)
    simpa using this
  · simp [hcoe]

theorem oriented
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits) :
    (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ F) (IgusaScheme.jFull p : F)⁻¹)
          ((jp : F) * ((IgusaScheme.jFull p : F)⁻¹) ^ p) = 0) ∧
    ((jp : F) * ((IgusaScheme.jFull p : F)⁻¹) ^ p - 1 ∈ W₀.nonunits) ∧
    (((jp : F) * ((IgusaScheme.jFull p : F)⁻¹) ^ p) ^ p - ((IgusaScheme.jFull p : F)⁻¹) ^ (p ^ 2 - 1)
        ∈ W₁.nonunits) ∧
    (((jp : F) * ((IgusaScheme.jFull p : F)⁻¹) ^ p) ^ p - ((IgusaScheme.jFull p : F)⁻¹) ^ (p ^ 2 - 1)
        ∉ W₀.nonunits) ∧
    (((((jp : F) * ((IgusaScheme.jFull p : F)⁻¹) ^ p) ^ p
        - ((IgusaScheme.jFull p : F)⁻¹) ^ (p ^ 2 - 1) : F) : LaurentSeries ℚ).coeff 0 = 1) ∧
    (∀ f ∈ W₀.nonunits, f * ((p : ℕ) : F)⁻¹ ∈ W₀) ∧
    (∀ f ∈ W₁.nonunits, f * ((p : ℕ) : F)⁻¹ ∈ W₁) := by
  obtain ⟨W'0, W'1, hne', hloc', hcomp', hh, ht1', hs', hcoeff'⟩ := pkg p (jp : F) hjp
  have hj0 : J ≠ 0 := IgusaScheme.jFull_ne_zero p
  have hj1 : J ^ (p ^ 2 - 1) - 1 ≠ 0 := jFull_pow_sub_one_ne_zero p
  have hgen0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₀ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₀ :=
    fun P hP => by simpa using hgen 0 P hP
  have hloc1 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W'1 ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W'1 :=
    fun P hP => by simpa using (hloc' 1).2.1 P hP
  have hloc0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W'0 ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W'0 :=
    fun P hP => by simpa using (hloc' 0).2.1 P hP
  have hp1' : ((p : ℕ) : F) ∈ W'1.nonunits := by simpa using (hloc' 1).1
  have hp0' : ((p : ℕ) : F) ∈ W'0.nonunits := by simpa using (hloc' 0).1
  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero

  have ht_eq : (jp : F) * (J⁻¹) ^ p - 1 = (J⁻¹) ^ p * ((jp : F) - J ^ p) := by
    rw [mul_sub, ← mul_pow, inv_mul_cancel₀ hj0, one_pow, mul_comm]

  have hW1 : W'1 = W₁ := by
    rcases hcomp_or hcomplete W'1 hp1' hloc1 with h | h
    · exfalso

      have hjinv : J⁻¹ ∈ W'1 := by
        have := (hloc1 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
      have ht1 : (jp : F) * (J⁻¹) ^ p - 1 ∈ W'1.nonunits := by
        rw [ht_eq]; exact mul_mem_nonunits_of_mem W'1 (pow_mem hjinv p) (h ▸ ht)
      exact not_mem_nonunits_witness W'1 p J hj0 hj1 hloc1 _ ht1 hs'
    · exact h
  have hW0 : W'0 = W₀ := by
    rcases hcomp_or hcomplete W'0 hp0' hloc0 with h | h
    · exact h
    · exact absurd (h.trans hW1.symm) hne'
  subst hW0 hW1
  exact ⟨hh, ht1', hs', not_mem_nonunits_witness W'0 p J hj0 hj1 hloc0 _ ht1', hcoeff',
    fun f hf => by simpa using (hloc' 0).2.2 f hf, fun f hf => by simpa using (hloc' 1).2.2 f hf⟩
where

  hcomp_or {F' : Type} [Field F'] {W₀' W₁' : ValuationSubring F'} {q : F'} {Q : ValuationSubring F' → Prop}
      (hc : ∀ V : ValuationSubring F', q ∈ V.nonunits → Q V → V = W₀' ∨ V = W₁')
      (V : ValuationSubring F') (h1 : q ∈ V.nonunits) (h2 : Q V) : V = W₀' ∨ V = W₁' := hc V h1 h2

theorem exists_mem_nonunits_not_dvd
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits)
    (φ : ↥(TwoChartIntegralModel.chartAlgInf ℤ F (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0) :
    ∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ F (IgusaScheme.jFull p)),
      (a : F) ∈ W₁.nonunits ∧ (a : F) ∉ W₀.nonunits ∧ ¬ (p : ℤ) ∣ φ a := by
  obtain ⟨⟨h, hmonic, heval⟩, -, hs, hs0, hcoeff, -, -⟩ :=
    oriented p jp hjp W₀ W₁ hgen hcomplete ht

  let B : Subalgebra ℤ F := Algebra.adjoin ℤ ({J⁻¹} : Set F)
  let uB : B := ⟨J⁻¹, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let aev : Polynomial ℤ →+* B := (Polynomial.aeval uB).toRingHom
  have hcomp : (algebraMap B F).comp aev = Polynomial.eval₂RingHom (algebraMap ℤ F) J⁻¹ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · change algebraMap B F (Polynomial.aeval uB (Polynomial.C c)) = _
      rw [Polynomial.aeval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        ← IsScalarTower.algebraMap_apply]
    · change algebraMap B F (Polynomial.aeval uB Polynomial.X) = _
      rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have htint : IsIntegral B ((jp : F) * J⁻¹ ^ p) := by
    refine ⟨h.map aev, hmonic.map aev, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact heval
  have htmem : (jp : F) * J⁻¹ ^ p ∈ TwoChartIntegralModel.chartAlgInf ℤ F J :=
    (TwoChartIntegralModel.mem_chartAlg_iff ℤ F).mpr htint
  have humem : J⁻¹ ∈ TwoChartIntegralModel.chartAlgInf ℤ F J :=
    TwoChartIntegralModel.subset_chartAlg ℤ F _ (Set.mem_singleton _)
  have hsmem : ((jp : F) * J⁻¹ ^ p) ^ p - J⁻¹ ^ (p ^ 2 - 1) ∈ TwoChartIntegralModel.chartAlgInf ℤ F J :=
    Subalgebra.sub_mem _ (Subalgebra.pow_mem _ htmem p) (Subalgebra.pow_mem _ humem _)
  refine ⟨⟨((jp : F) * J⁻¹ ^ p) ^ p - J⁻¹ ^ (p ^ 2 - 1), hsmem⟩, hs, hs0, ?_⟩
  have h1 : φ ⟨((jp : F) * J⁻¹ ^ p) ^ p - J⁻¹ ^ (p ^ 2 - 1), hsmem⟩ = 1 := by
    have h1' : ((φ ⟨((jp : F) * J⁻¹ ^ p) ^ p - J⁻¹ ^ (p ^ 2 - 1), hsmem⟩ : ℤ) : ℚ) = 1 := by
      rw [hφ]; exact hcoeff
    exact_mod_cast h1'
  rw [h1]
  intro hdvd
  have : p ∣ 1 := by exact_mod_cast hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)

end LevelP

end ModularCurve.DRModel.C4

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve"

section ConclusionOne

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull p) : Type)
set_option quotPrecheck false in
local notation "J" => (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))
set_option quotPrecheck false in
local notation "A" => (↥(TwoChartIntegralModel.chartAlgInf ℤ (↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p)) : Type)

theorem transcendental_int_jFull : Transcendental ℤ (IgusaScheme.jFull p : F) := by
  have htjℚ : Transcendental ℚ (IgusaScheme.jFull p : F) := by
    intro halg
    obtain ⟨q, hq, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨q, hq, ?_⟩
    have h0 : (algebraMap F (LaurentSeries ℚ)) ((Polynomial.aeval (IgusaScheme.jFull p : F)) q) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap F (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from IgusaScheme.coe_jFull p] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  exact fun h => htjℚ ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mp h)

theorem adjoin_coe_mem (W : ValuationSubring F) (hu : (IgusaScheme.jFull p : F)⁻¹ ∈ W)
    (b : ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull p : F)⁻¹} : Set F))) : (b : F) ∈ W := by
  have hle : Algebra.adjoin ℤ ({(IgusaScheme.jFull p : F)⁻¹} : Set F) ≤ subalgebraOfSubring W.toSubring :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show (IgusaScheme.jFull p : F)⁻¹ ∈
      subalgebraOfSubring W.toSubring from mem_subalgebraOfSubring.mpr hu))
  exact mem_subalgebraOfSubring.mp (hle b.2)

theorem coe_mem_of_inv_mem (W : ValuationSubring F) (hu : (IgusaScheme.jFull p : F)⁻¹ ∈ W) (a : A) :
    (a : F) ∈ W := by
  let B : Subalgebra ℤ F := Algebra.adjoin ℤ ({(IgusaScheme.jFull p : F)⁻¹} : Set F)
  have hBW : ∀ b : B, (b : F) ∈ W := adjoin_coe_mem p W hu
  let ι : B →+* W :=
    { toFun := fun b => ⟨b, hBW b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨q, hq, hev⟩ := (TwoChartIntegralModel.mem_chartAlg_iff ℤ F).mp a.2
  have hint : IsIntegral W (a : F) := by
    refine ⟨q.map ι, hq.map ι, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hev
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

variable {p} in

noncomputable def toW (W : ValuationSubring F) (h : ∀ a : A, (a : F) ∈ W) : A →+* W where
  toFun a := ⟨a, h a⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {p} in

noncomputable def qOf (W : ValuationSubring F) (h : ∀ a : A, (a : F) ∈ W) : Ideal A :=
  (IsLocalRing.maximalIdeal W).comap (toW W h)

variable {p} in
theorem mem_qOf {W : ValuationSubring F} {h : ∀ a : A, (a : F) ∈ W} {a : A} :
    a ∈ qOf W h ↔ (a : F) ∈ W.nonunits := by
  rw [qOf, Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun ha => ⟨h a, ha⟩, fun ⟨_, ha⟩ => ha⟩

variable {p} in
scoped instance qOf_isPrime {W : ValuationSubring F} {h : ∀ a : A, (a : F) ∈ W} : (qOf W h).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_span_of_mem_nonunits (W : ValuationSubring F)
    (hgenW : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ W ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ W)
    (b : ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull p : F)⁻¹} : Set F))) (hb : (b : F) ∈ W.nonunits) :
    b ∈ Ideal.span {((p : ℕ) : ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull p : F)⁻¹} : Set F)))} := by
  have hj0 : J ≠ 0 := IgusaScheme.jFull_ne_zero p
  have hu0 : J⁻¹ ≠ 0 := inv_ne_zero hj0
  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  obtain ⟨hjW, -⟩ := hgenW Polynomial.X hX
  rw [Polynomial.eval₂_X] at hjW

  have hbmem : (b : F) ∈ (Polynomial.aeval J⁻¹ : Polynomial ℤ →ₐ[ℤ] F).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact b.2
  obtain ⟨g, hg⟩ := hbmem
  have hg' : Polynomial.aeval J⁻¹ g = (b : F) := hg
  by_cases hbar : g.map (Int.castRingHom (ZMod p)) = 0
  ·
    have hdvd : Polynomial.C (p : ℤ) ∣ g := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have := congrArg (fun q => q.coeff n) hbar
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
    obtain ⟨g₁, rfl⟩ := hdvd
    refine Ideal.mem_span_singleton'.mpr ⟨⟨Polynomial.aeval J⁻¹ g₁, Polynomial.aeval_mem_adjoin_singleton ℤ _⟩, ?_⟩
    apply Subtype.ext
    change Polynomial.aeval J⁻¹ g₁ * (((p : ℕ) : ↥(Algebra.adjoin ℤ ({J⁻¹} : Set F))) : F) = (b : F)
    rw [← hg', map_mul, Polynomial.aeval_C, mul_comm]
    simp
  ·
    exfalso
    haveI : Invertible (J⁻¹) := invertibleOfNonzero hu0
    have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap ℤ F) J⁻¹ g
    have hinvOf : (⅟(J⁻¹) : F) = J := by rw [invOf_eq_inv, inv_inv]
    rw [hinvOf] at hrev
    have hrevbar : (Polynomial.reverse g).map (Int.castRingHom (ZMod p)) ≠ 0 := by
      intro h0
      apply hbar
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      by_cases hk : k ≤ g.natDegree
      · have := congrArg (fun q => q.coeff (Polynomial.revAt g.natDegree k)) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_reverse,
          Polynomial.revAt_invol] at this
        exact this
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), map_zero]
    obtain ⟨-, hRinvW⟩ := hgenW (Polynomial.reverse g) hrevbar
    have hR0 : Polynomial.eval₂ (algebraMap ℤ F) J (Polynomial.reverse g) ≠ 0 := by
      intro h0
      apply transcendental_int_jFull p
      refine ⟨Polynomial.reverse g, fun h => hrevbar (by rw [h, Polynomial.map_zero]), ?_⟩
      rw [Polynomial.aeval_def]; exact h0
    have hbF : (b : F) = Polynomial.eval₂ (algebraMap ℤ F) J (Polynomial.reverse g) * J⁻¹ ^ g.natDegree := by
      rw [← hg', Polynomial.aeval_def, ← hrev]
    have hb0 : (b : F) ≠ 0 := by rw [hbF]; exact mul_ne_zero hR0 (pow_ne_zero _ hu0)
    have hbinv : (b : F)⁻¹ ∈ W := by
      rw [hbF, mul_inv, ← inv_pow, inv_inv]
      exact mul_mem hRinvW (pow_mem hjW _)
    exact not_mem_nonunits_of_inv_mem W hb0 hbinv hb

theorem qOf_mem_minimalPrimes (W : ValuationSubring F) (hAW : ∀ a : A, (a : F) ∈ W)
    (hpW : ((p : ℕ) : F) ∈ W.nonunits)
    (hgenW : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ W ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ W) :
    qOf W hAW ∈ (Ideal.span {((p : ℕ) : A)}).minimalPrimes := by
  let B : Subalgebra ℤ F := Algebra.adjoin ℤ ({J⁻¹} : Set F)
  have hBA : B ≤ TwoChartIntegralModel.chartAlgInf ℤ F J :=
    TwoChartIntegralModel.adjoin_le_chartAlg ℤ F _
  have hpq : ((p : ℕ) : A) ∈ qOf W hAW := by
    rw [mem_qOf]
    have : (((p : ℕ) : A) : F) = ((p : ℕ) : F) := by simp
    rw [this]; exact hpW
  obtain ⟨P', hP'min, hP'le⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {((p : ℕ) : A)} ≤ qOf W hAW from (Ideal.span_singleton_le_iff_mem _).mpr hpq)
  haveI hP'prime : P'.IsPrime := hP'min.1.1
  suffices h : P' = qOf W hAW by rw [← h]; exact hP'min
  by_contra hne
  have hlt : P' < qOf W hAW := lt_of_le_of_ne hP'le hne
  obtain ⟨x, hxq, hxP'⟩ := SetLike.exists_of_lt hlt
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  have hint : IsIntegral B x := by
    have hx : IsIntegral B ((x : A) : F) := (TwoChartIntegralModel.mem_chartAlg_iff ℤ F).mp x.2
    let f : A →ₐ[B] F :=
      { (TwoChartIntegralModel.chartAlgInf ℤ F J).val.toRingHom with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp hx
  have hlt' := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := B) hP'le ⟨hxq, hxP'⟩ hint
  have h1 : Ideal.span {((p : ℕ) : B)} ≤ P'.comap (algebraMap B A) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP'min.1.2 (Ideal.subset_span rfl)
  have h2 : (qOf W hAW).comap (algebraMap B A) ≤ Ideal.span {((p : ℕ) : B)} := by
    intro b hb
    rw [Ideal.mem_comap, mem_qOf] at hb
    exact mem_span_of_mem_nonunits p W hgenW b hb
  exact absurd (lt_of_lt_of_le hlt' (h2.trans h1)) (lt_irrefl _)

theorem dvd_of_mem_nonunits
    (hH : IsReduced (A ⧸ Ideal.span {((p : ℕ) : A)}) ∧ (Ideal.span {((p : ℕ) : A)}).minimalPrimes.ncard = 2)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hp₀ : ((p : ℕ) : F) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : F) ∈ W₁.nonunits)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits)
    (φ : A →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0)
    (a : A) (ha : (a : F) ∈ W₀.nonunits) : (p : ℤ) ∣ φ a := by
  have hgen0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₀ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₀ :=
    fun P hP => by simpa using hgen 0 P hP
  have hgen1 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₁ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₁ :=
    fun P hP => by simpa using hgen 1 P hP
  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hu0 : J⁻¹ ∈ W₀ := by have := (hgen0 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
  have hu1 : J⁻¹ ∈ W₁ := by have := (hgen1 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
  have hAW₀ : ∀ a : A, (a : F) ∈ W₀ := coe_mem_of_inv_mem p W₀ hu0
  have hAW₁ : ∀ a : A, (a : F) ∈ W₁ := coe_mem_of_inv_mem p W₁ hu1

  obtain ⟨s, hs1, hs0, hφs⟩ := exists_mem_nonunits_not_dvd p jp hjp W₀ W₁ hgen hcomplete ht φ hφ

  have hmin0 := qOf_mem_minimalPrimes p W₀ hAW₀ hp₀ hgen0
  have hmin1 := qOf_mem_minimalPrimes p W₁ hAW₁ hp₁ hgen1
  have hneq : qOf W₀ hAW₀ ≠ qOf W₁ hAW₁ := by
    intro h
    have : s ∈ qOf W₁ hAW₁ := mem_qOf.mpr hs1
    rw [← h, mem_qOf] at this
    exact hs0 this
  have hpair : ({qOf W₀ hAW₀, qOf W₁ hAW₁} : Set (Ideal A)) = (Ideal.span {((p : ℕ) : A)}).minimalPrimes := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.finite_of_ncard_ne_zero (by rw [hH.2]; decide))
    · intro q hq
      rcases hq with rfl | rfl
      · exact hmin0
      · exact hmin1
    · rw [hH.2, Set.ncard_pair hneq]
  have hrad : (Ideal.span {((p : ℕ) : A)}).radical = Ideal.span {((p : ℕ) : A)} :=
    Ideal.radical_eq_iff.mpr ((Ideal.isRadical_iff_quotient_reduced _).mpr hH.1)
  have hinf : qOf W₀ hAW₀ ⊓ qOf W₁ hAW₁ = Ideal.span {((p : ℕ) : A)} := by
    rw [← sInf_pair, hpair, Ideal.sInf_minimalPrimes, hrad]

  have has : a * s ∈ Ideal.span {((p : ℕ) : A)} := by
    rw [← hinf]
    exact ⟨Ideal.mul_mem_right _ _ (mem_qOf.mpr ha), Ideal.mul_mem_left _ _ (mem_qOf.mpr hs1)⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp has
  have hφeq : φ b * (p : ℤ) = φ a * φ s := by
    have := congrArg φ hb
    rwa [map_mul, map_mul, map_natCast] at this
  have hdvd : (p : ℤ) ∣ φ a * φ s := ⟨φ b, by rw [← hφeq, mul_comm]⟩
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd hdvd with h | h
  · exact h
  · exact absurd h hφs

end ConclusionOne

end ModularCurve.DRModel.C4
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
namespace QExp
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve WithZero"
open scoped Classical

noncomputable section

section QAdic

def 𝒪 : Subring (LaurentSeries ℚ) := (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).integer

theorem mem_𝒪_iff (f : LaurentSeries ℚ) : f ∈ 𝒪 ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  rw [𝒪, Valuation.mem_integer_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℚ) (D := 0) (f := f)
  simpa using h

theorem exists_powerSeries_of_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) :
    ∃ F : PowerSeries ℚ, (F : LaurentSeries ℚ) = f :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) f).mp hf

theorem coe_powerSeries_mem_𝒪 (F : PowerSeries ℚ) : (F : LaurentSeries ℚ) ∈ 𝒪 :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) (F : LaurentSeries ℚ)).mpr ⟨F, rfl⟩

theorem coeff_zero_coe_powerSeries (F : PowerSeries ℚ) :
    (F : LaurentSeries ℚ).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

theorem C_mem_𝒪 (c : ℚ) : (HahnSeries.C c : LaurentSeries ℚ) ∈ 𝒪 := by
  rw [mem_𝒪_iff]
  intro n hn
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne]

def ρ : ↥𝒪 →+* ℚ where
  toFun f := (f : LaurentSeries ℚ).coeff 0
  map_one' := by simp
  map_mul' f g := by
    obtain ⟨F, hF⟩ := exists_powerSeries_of_mem_𝒪 f.2
    obtain ⟨G, hG⟩ := exists_powerSeries_of_mem_𝒪 g.2
    change ((f : LaurentSeries ℚ) * (g : LaurentSeries ℚ)).coeff 0
      = (f : LaurentSeries ℚ).coeff 0 * (g : LaurentSeries ℚ).coeff 0
    rw [← hF, ← hG, ← map_mul]
    change ((F * G : PowerSeries ℚ) : LaurentSeries ℚ).coeff 0
      = (F : LaurentSeries ℚ).coeff 0 * (G : LaurentSeries ℚ).coeff 0
    rw [coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, map_mul]
  map_zero' := by simp
  map_add' f g := by simp

@[scoped simp] theorem ρ_apply (f : ↥𝒪) : ρ f = (f : LaurentSeries ℚ).coeff 0 := rfl

theorem ρ_C (c : ℚ) : ρ ⟨HahnSeries.C c, C_mem_𝒪 c⟩ = c := by
  change (HahnSeries.C c : LaurentSeries ℚ).coeff 0 = c
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem coeff_zero_single_mul_of_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) {m : ℤ} (hm : 0 < m) :
    (HahnSeries.single m (1 : ℚ) * f).coeff 0 = 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul]
  exact (mem_𝒪_iff f).mp hf _ (by omega)

theorem single_mul_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) {m : ℤ} (hm : 0 ≤ m) :
    HahnSeries.single m (1 : ℚ) * f ∈ 𝒪 := by
  rw [mem_𝒪_iff] at hf ⊢
  intro n hn
  rw [HahnSeries.coeff_single_mul, one_mul]
  exact hf _ (by omega)

end QAdic
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"

section OUnits

theorem inv_mem_𝒪_and_coeff {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) (h0 : f.coeff 0 ≠ 0) :
    f⁻¹ ∈ 𝒪 ∧ f⁻¹.coeff 0 = (f.coeff 0)⁻¹ := by
  obtain ⟨Φ, hΦ⟩ := exists_powerSeries_of_mem_𝒪 hf
  have hc : PowerSeries.constantCoeff Φ ≠ 0 := by
    rwa [← coeff_zero_coe_powerSeries, hΦ]
  have hinv : f⁻¹ = ((Φ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
    have hf0 : f ≠ 0 := fun h => h0 (by rw [h, HahnSeries.coeff_zero])
    apply mul_left_cancel₀ hf0
    rw [mul_inv_cancel₀ hf0, ← hΦ, ← map_mul, PowerSeries.mul_inv_cancel Φ hc, map_one]
  refine ⟨by rw [hinv]; exact coe_powerSeries_mem_𝒪 _, ?_⟩
  rw [hinv, coeff_zero_coe_powerSeries, PowerSeries.constantCoeff_inv, ← hΦ,
    coeff_zero_coe_powerSeries]

def 𝔮 : LaurentSeries ℚ := HahnSeries.single (1 : ℤ) 1

theorem 𝔮_pow (n : ℕ) : 𝔮 ^ n = HahnSeries.single (n : ℤ) (1 : ℚ) := by
  rw [𝔮, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

theorem 𝔮_pow_mem_𝒪 (n : ℕ) : 𝔮 ^ n ∈ 𝒪 := by
  rw [𝔮_pow, ← mul_one (HahnSeries.single (n : ℤ) (1 : ℚ))]
  exact single_mul_mem_𝒪 (Subring.one_mem _) (by positivity)

theorem coeff_zero_𝔮_pow_mul {n : ℕ} (hn : 0 < n) {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) :
    (𝔮 ^ n * f).coeff 0 = 0 := by
  rw [𝔮_pow]; exact coeff_zero_single_mul_of_mem_𝒪 hf (by exact_mod_cast hn)

theorem 𝔮_pow_mul_mem_𝒪 (n : ℕ) {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) : 𝔮 ^ n * f ∈ 𝒪 :=
  Subring.mul_mem _ (𝔮_pow_mem_𝒪 n) hf

theorem 𝔮_ne_zero : 𝔮 ≠ 0 := by
  rw [𝔮]; exact HahnSeries.single_ne_zero one_ne_zero

theorem 𝔮_mul_jq : 𝔮 * jq = ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [𝔮, jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem 𝔮_mul_jq_mem_𝒪 : 𝔮 * jq ∈ 𝒪 := by rw [𝔮_mul_jq]; exact coe_powerSeries_mem_𝒪 _

theorem coeff_zero_𝔮_mul_jq : (𝔮 * jq).coeff 0 = 1 := by
  rw [𝔮_mul_jq, coeff_zero_coe_powerSeries, constantCoeff_jNumQ]

theorem jq_inv_eq : jq⁻¹ = 𝔮 ^ 1 * (𝔮 * jq)⁻¹ := by
  rw [pow_one, mul_inv, ← mul_assoc, mul_inv_cancel₀ 𝔮_ne_zero, one_mul]

theorem jq_inv_mem_𝒪_and_coeff : jq⁻¹ ∈ 𝒪 ∧ jq⁻¹.coeff 0 = 0 := by
  have h := inv_mem_𝒪_and_coeff 𝔮_mul_jq_mem_𝒪 (by rw [coeff_zero_𝔮_mul_jq]; exact one_ne_zero)
  rw [jq_inv_eq]
  exact ⟨𝔮_pow_mul_mem_𝒪 1 h.1, coeff_zero_𝔮_pow_mul one_pos h.1⟩

end OUnits
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"

end ModularCurve.DRModel.C4.QExp
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve"

section ResidueRational

variable {K : Type} [Field K]

theorem exists_sub_eval₂_mem_nonunits (p : ℕ) [Fact p.Prime] (W : ValuationSubring K) (j : K) (hj0 : j ≠ 0)
    (hpW : ((p : ℕ) : K) ∈ W.nonunits)
    (hgenW : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ K) j P ∈ W ∧ (Polynomial.eval₂ (algebraMap ℤ K) j P)⁻¹ ∈ W)
    (hjt : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 → Polynomial.eval₂ (algebraMap ℤ K) j P ≠ 0)
    (h8 : ∀ x : K, x ∈ W → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ K) j Q - Polynomial.eval₂ (algebraMap ℤ K) j P ∈ W.nonunits)
    (x : K) (Pb : Polynomial (Polynomial ℤ)) (hPm : Pb.Monic)
    (hPb : Pb.eval₂ (Polynomial.aeval (R := ℤ) j⁻¹).toRingHom x = 0) :
    ∃ G : Polynomial ℤ, x - Polynomial.eval₂ (algebraMap ℤ K) j⁻¹ G ∈ W.nonunits := by
  classical
  have hprime : p.Prime := Fact.out

  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  obtain ⟨hjW, hjinvW⟩ := hgenW Polynomial.X hX
  rw [Polynomial.eval₂_X] at hjW hjinvW
  set jW : W := ⟨j, hjW⟩ with hjWdef
  set uW : W := ⟨j⁻¹, hjinvW⟩ with huWdef

  have hevK : ∀ (w : W) (P : Polynomial ℤ),
      ((Polynomial.eval₂ (algebraMap ℤ W) w P : W) : K) = Polynomial.eval₂ (algebraMap ℤ K) (w : K) P := by
    intro w P
    change W.subtype (Polynomial.eval₂ (algebraMap ℤ W) w P) = _
    rw [Polynomial.hom_eval₂]
    congr 1 <;> exact RingHom.ext_int _ _
  set θ : Polynomial ℤ →+* W := Polynomial.eval₂RingHom (algebraMap ℤ W) uW with hθ
  have hθK : W.subtype.comp θ = (Polynomial.aeval (R := ℤ) j⁻¹).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_C]
      simp
    · rw [RingHom.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl

  have hxint : IsIntegral W x := by
    refine ⟨Pb.map θ, hPm.map θ, ?_⟩
    rw [Polynomial.eval₂_map, show algebraMap W K = W.subtype from rfl, hθK, hPb]
  obtain ⟨xW, hxW⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint

  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField W) = 0 := by
    obtain ⟨h1, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpW
    have h3 : ((p : ℕ) : W) ∈ IsLocalRing.maximalIdeal W := by
      convert h2 using 1 <;> exact Subtype.ext (by simp)
    rw [← map_natCast (IsLocalRing.residue W), IsLocalRing.residue_eq_zero_iff]
    exact h3
  haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hprime).mpr hp0
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField W) := ZMod.algebra _ p
  have hjy : (IsLocalRing.residue W jW) * (IsLocalRing.residue W uW) = 1 := by
    rw [← map_mul, show jW * uW = 1 from Subtype.ext (mul_inv_cancel₀ hj0), map_one]
  have hy0 : (IsLocalRing.residue W uW) ≠ 0 := right_ne_zero_of_mul_eq_one hjy
  have hjb0 : (IsLocalRing.residue W jW) ≠ 0 := left_ne_zero_of_mul_eq_one hjy
  have hjyd : ∀ d : ℕ, (IsLocalRing.residue W jW) ^ d * (IsLocalRing.residue W uW) ^ d = 1 := fun d => by rw [← mul_pow, hjy, one_pow]

  have hev : ∀ (w : W) (P : Polynomial ℤ),
      IsLocalRing.residue W (Polynomial.eval₂ (algebraMap ℤ W) w P) =
        Polynomial.aeval (IsLocalRing.residue W w) (P.map (Int.castRingHom (ZMod p))) := by
    intro w P
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1 <;> exact RingHom.ext_int _ _

  have hjbt : Transcendental (ZMod p) (IsLocalRing.residue W jW) := by
    rintro ⟨q, hq0, hq⟩
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) q
    have hQbar : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by rw [hQ]; exact hq0
    obtain ⟨-, hQinvW⟩ := hgenW Q hQbar
    have hunit : IsUnit (Polynomial.eval₂ (algebraMap ℤ W) jW Q) := by
      refine IsUnit.of_mul_eq_one ⟨(Polynomial.eval₂ (algebraMap ℤ K) j Q)⁻¹, hQinvW⟩ ?_
      apply Subtype.ext
      change ((Polynomial.eval₂ (algebraMap ℤ W) jW Q : W) : K) * (Polynomial.eval₂ (algebraMap ℤ K) j Q)⁻¹ = 1
      rw [hevK]
      exact mul_inv_cancel₀ (hjt Q hQbar)
    have hres0 : IsLocalRing.residue W (Polynomial.eval₂ (algebraMap ℤ W) jW Q) = 0 := by
      rw [hev, hQ]; exact hq
    rw [IsLocalRing.residue_eq_zero_iff] at hres0
    exact (IsLocalRing.mem_maximalIdeal _).mp hres0 hunit
  have hyt : Transcendental (ZMod p) (IsLocalRing.residue W uW) := by
    have hyeq : (IsLocalRing.residue W uW) = (IsLocalRing.residue W jW)⁻¹ := eq_inv_of_mul_eq_one_right hjy
    rw [hyeq]
    exact fun h => hjbt (IsAlgebraic.inv_iff.mp h)

  set S : Subalgebra (ZMod p) (IsLocalRing.ResidueField W) := (Polynomial.aeval (R := ZMod p) (IsLocalRing.residue W uW)).range with hS
  have hinj : Function.Injective (Polynomial.aeval (R := ZMod p) (IsLocalRing.residue W uW)) := transcendental_iff_injective.mp hyt
  let e : Polynomial (ZMod p) ≃ₐ[ZMod p] S := AlgEquiv.ofInjective _ hinj
  haveI : UniqueFactorizationMonoid S := MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance
  haveI : FaithfulSMul S (IsLocalRing.ResidueField W) :=
    (faithfulSMul_iff_algebraMap_injective S (IsLocalRing.ResidueField W)).mpr Subtype.val_injective
  haveI : IsFractionRing S (IsLocalRing.ResidueField W) := by
    refine IsFractionRing.of_field S (IsLocalRing.ResidueField W) (fun z => ?_)
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨P, Q, hQ, hPQ⟩ := h8 w w.2
    set Qb := Q.map (Int.castRingHom (ZMod p)) with hQb
    set Pbb := P.map (Int.castRingHom (ZMod p)) with hPbb

    have hrel : IsLocalRing.residue W w * Polynomial.aeval (IsLocalRing.residue W jW) Qb - Polynomial.aeval (IsLocalRing.residue W jW) Pbb = 0 := by
      rw [hQb, hPbb, ← hev, ← hev, ← map_mul, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      obtain ⟨hm1, hm2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hPQ
      convert hm2 using 1
      apply Subtype.ext
      simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hevK]
      rfl

    haveI : Invertible (IsLocalRing.residue W jW) := invertibleOfNonzero hjb0
    have hinvOf : (⅟(IsLocalRing.residue W jW) : IsLocalRing.ResidueField W) = (IsLocalRing.residue W uW) := by
      rw [invOf_eq_inv]; exact (eq_inv_of_mul_eq_one_right hjy).symm
    have hrevQ : Polynomial.aeval (IsLocalRing.residue W uW) Qb.reverse * (IsLocalRing.residue W jW) ^ Qb.natDegree = Polynomial.aeval (IsLocalRing.residue W jW) Qb := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← hinvOf]
      exact Polynomial.eval₂_reverse_mul_pow _ (IsLocalRing.residue W jW) Qb
    have hrevP : Polynomial.aeval (IsLocalRing.residue W uW) Pbb.reverse * (IsLocalRing.residue W jW) ^ Pbb.natDegree = Polynomial.aeval (IsLocalRing.residue W jW) Pbb := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← hinvOf]
      exact Polynomial.eval₂_reverse_mul_pow _ (IsLocalRing.residue W jW) Pbb
    have h1 : IsLocalRing.residue W w * (Polynomial.aeval (IsLocalRing.residue W uW) Qb.reverse * (IsLocalRing.residue W jW) ^ Qb.natDegree) =
        Polynomial.aeval (IsLocalRing.residue W uW) Pbb.reverse * (IsLocalRing.residue W jW) ^ Pbb.natDegree := by
      rw [hrevQ, hrevP]; exact sub_eq_zero.mp hrel
    have key : IsLocalRing.residue W w * (Polynomial.aeval (IsLocalRing.residue W uW) Qb.reverse * (IsLocalRing.residue W uW) ^ Pbb.natDegree) =
        Polynomial.aeval (IsLocalRing.residue W uW) Pbb.reverse * (IsLocalRing.residue W uW) ^ Qb.natDegree := by
      linear_combination ((IsLocalRing.residue W uW) ^ Qb.natDegree * (IsLocalRing.residue W uW) ^ Pbb.natDegree) * h1
        - (IsLocalRing.residue W w * Polynomial.aeval (IsLocalRing.residue W uW) Qb.reverse * (IsLocalRing.residue W uW) ^ Pbb.natDegree) * hjyd Qb.natDegree
        + (Polynomial.aeval (IsLocalRing.residue W uW) Pbb.reverse * (IsLocalRing.residue W uW) ^ Qb.natDegree) * hjyd Pbb.natDegree
    have hb0 : Polynomial.aeval (IsLocalRing.residue W uW) Qb.reverse * (IsLocalRing.residue W uW) ^ Pbb.natDegree ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ hy0)
      intro h0
      have : Qb.reverse = 0 := hinj (by rw [h0, map_zero])
      exact hQ (Polynomial.reverse_eq_zero.mp this)
    refine ⟨⟨Polynomial.aeval (IsLocalRing.residue W uW) (Pbb.reverse * Polynomial.X ^ Qb.natDegree), ⟨_, rfl⟩⟩,
      ⟨Polynomial.aeval (IsLocalRing.residue W uW) (Qb.reverse * Polynomial.X ^ Pbb.natDegree), ⟨_, rfl⟩⟩, ?_⟩
    change IsLocalRing.residue W w = Polynomial.aeval (IsLocalRing.residue W uW) (Pbb.reverse * Polynomial.X ^ Qb.natDegree) /
      Polynomial.aeval (IsLocalRing.residue W uW) (Qb.reverse * Polynomial.X ^ Pbb.natDegree)
    rw [map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X]
    exact eq_div_of_mul_eq hb0 key

  set θκ : Polynomial ℤ →+* S :=
    (e.toAlgHom.toRingHom).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) with hθκ
  have hθκ_coe : ∀ G : Polynomial ℤ, ((θκ G : S) : IsLocalRing.ResidueField W) =
      Polynomial.aeval (IsLocalRing.residue W uW) (G.map (Int.castRingHom (ZMod p))) := by
    intro G
    change ((e (G.map (Int.castRingHom (ZMod p))) : S) : IsLocalRing.ResidueField W) = _
    exact AlgEquiv.ofInjective_apply _ hinj _
  have hcompat : (algebraMap S (IsLocalRing.ResidueField W)).comp θκ = (IsLocalRing.residue W).comp θ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · change ((θκ (Polynomial.C c) : S) : IsLocalRing.ResidueField W) = IsLocalRing.residue W (θ (Polynomial.C c))
      rw [hθκ_coe, Polynomial.map_C, Polynomial.aeval_C, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      simp
    · change ((θκ Polynomial.X : S) : IsLocalRing.ResidueField W) = IsLocalRing.residue W (θ Polynomial.X)
      rw [hθκ_coe, Polynomial.map_X, Polynomial.aeval_X, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hroot : Pb.eval₂ θ xW = 0 := by
    apply Subtype.val_injective
    change W.subtype (Pb.eval₂ θ xW) = ((0 : W) : K)
    rw [Polynomial.hom_eval₂, hθK, show W.subtype xW = x from hxW, hPb]
    simp
  have hint : IsIntegral S (IsLocalRing.residue W xW) := by
    refine ⟨Pb.map θκ, hPm.map θκ, ?_⟩
    rw [Polynomial.eval₂_map, hcompat, ← Polynomial.hom_eval₂, hroot, map_zero]
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨Gb, hGb⟩ := (AlgHom.mem_range _).mp s.2
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) Gb
  refine ⟨G, ?_⟩
  have hres0 : IsLocalRing.residue W (xW - θ G) = 0 := by
    rw [map_sub, hθ, Polynomial.coe_eval₂RingHom, hev, hG, hGb]
    change IsLocalRing.residue W xW - algebraMap S _ s = 0
    rw [hs, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hres0
  have hcoe : ((xW - θ G : W) : K) = x - Polynomial.eval₂ (algebraMap ℤ K) j⁻¹ G := by
    rw [AddSubgroupClass.coe_sub, show ((xW : W) : K) = x from hxW, hθ, Polynomial.coe_eval₂RingHom, hevK]
  rw [← hcoe]
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨(xW - θ G).2, by first | exact hres0 | simpa using hres0 | simpa [← AddSubgroupClass.coe_sub] using hres0 | (convert hres0 using 2; apply Subtype.ext; simp)⟩

end ResidueRational
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

end ModularCurve.DRModel.C4
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve"

section Enum

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull p) : Type)
set_option quotPrecheck false in
local notation "J" => (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))
set_option quotPrecheck false in
local notation "A" => (↥(TwoChartIntegralModel.chartAlgInf ℤ (↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p)) : Type)

theorem exists_bivariate_of_mem_chartAlgInf (a : A) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
      P.eval₂ (Polynomial.aeval (R := ℤ) (J⁻¹ : F)).toRingHom (a : F) = 0 := by
  obtain ⟨Q, hQm, hQ⟩ := (TwoChartIntegralModel.mem_chartAlg_iff ℤ F).mp a.2
  set Q' : Polynomial F := Q.map (algebraMap ↥(Algebra.adjoin ℤ ({(J⁻¹ : F)} : Set F)) F) with hQ'
  have hQ'm : Q'.Monic := hQm.map _
  have hlifts : Q' ∈ Polynomial.lifts (Polynomial.aeval (R := ℤ) (J⁻¹ : F)).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQ', Polynomial.coeff_map]
    have hmem : ((Q.coeff n : ↥(Algebra.adjoin ℤ ({(J⁻¹ : F)} : Set F))) : F) ∈
        (Polynomial.aeval (R := ℤ) (J⁻¹ : F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (Q.coeff n).2
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQ'm
  refine ⟨P, hPm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap, hQ', Polynomial.eval_map, hQ]

theorem phi_jInvChartInf_eq_zero
    (φ : A →ₐ[ℤ] ℤ) (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0) :
    φ (TwoChartIntegralModel.jInvChartInf ℤ F J) = 0 := by
  have h := hφ (TwoChartIntegralModel.jInvChartInf ℤ F J)
  have hcoe : (((TwoChartIntegralModel.jInvChartInf ℤ F J : A) : F) : LaurentSeries ℚ) = jq⁻¹ := by
    change (algebraMap F (LaurentSeries ℚ)) (J⁻¹) = jq⁻¹
    rw [map_inv₀, show (algebraMap F (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from IgusaScheme.coe_jFull p]
  rw [hcoe, QExp.jq_inv_mem_𝒪_and_coeff.2] at h
  exact_mod_cast h

theorem inf_qOf_eq_span
    (hH : IsReduced (A ⧸ Ideal.span {((p : ℕ) : A)}) ∧ (Ideal.span {((p : ℕ) : A)}).minimalPrimes.ncard = 2)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hp₀ : ((p : ℕ) : F) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : F) ∈ W₁.nonunits)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits)
    (φ : A →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0)
    (hAW₀ : ∀ a : A, (a : F) ∈ W₀) (hAW₁ : ∀ a : A, (a : F) ∈ W₁) :
    qOf W₀ hAW₀ ⊓ qOf W₁ hAW₁ = Ideal.span {((p : ℕ) : A)} := by
  have hgen0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₀ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₀ :=
    fun P hP => by simpa using hgen 0 P hP
  have hgen1 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₁ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₁ :=
    fun P hP => by simpa using hgen 1 P hP
  obtain ⟨s, hs1, hs0, -⟩ := exists_mem_nonunits_not_dvd p jp hjp W₀ W₁ hgen hcomplete ht φ hφ
  have hmin0 := qOf_mem_minimalPrimes p W₀ hAW₀ hp₀ hgen0
  have hmin1 := qOf_mem_minimalPrimes p W₁ hAW₁ hp₁ hgen1
  have hneq : qOf W₀ hAW₀ ≠ qOf W₁ hAW₁ := by
    intro h
    have : s ∈ qOf W₁ hAW₁ := mem_qOf.mpr hs1
    rw [← h, mem_qOf] at this
    exact hs0 this
  have hpair : ({qOf W₀ hAW₀, qOf W₁ hAW₁} : Set (Ideal A)) = (Ideal.span {((p : ℕ) : A)}).minimalPrimes := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.finite_of_ncard_ne_zero (by rw [hH.2]; decide))
    · intro q hq
      rcases hq with rfl | rfl
      · exact hmin0
      · exact hmin1
    · rw [hH.2, Set.ncard_pair hneq]
  have hrad : (Ideal.span {((p : ℕ) : A)}).radical = Ideal.span {((p : ℕ) : A)} :=
    Ideal.radical_eq_iff.mpr ((Ideal.isRadical_iff_quotient_reduced _).mpr hH.1)
  rw [← sInf_pair, hpair, Ideal.sInf_minimalPrimes, hrad]

theorem residue_rational_W₀
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits) :
    ∀ x : F, x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      x * Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) Q
        - Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ W₀.nonunits := by
  obtain ⟨jp', W'0, W'1, hjp', hp'0, -, -, hgen', -, ht', h8, -⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨-, -, hs1, -, -, -, -⟩ := oriented p jp hjp W₀ W₁ hgen hcomplete ht
  have hj0 : J ≠ 0 := IgusaScheme.jFull_ne_zero p
  have hj1 : J ^ (p ^ 2 - 1) - 1 ≠ 0 := jFull_pow_sub_one_ne_zero p
  have hjpeq : (jp' : F) = (jp : F) := Subtype.ext (hjp'.trans hjp.symm)
  have hgen'0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W'0 ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W'0 :=
    fun P hP => by simpa using hgen' 0 P hP
  have hgen1 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₁ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₁ :=
    fun P hP => by simpa using hgen 1 P hP
  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  rcases hcomplete W'0 hp'0 hgen'0 with h | h
  · subst h
    exact h8
  · exfalso
    rw [h] at ht'

    have hjinv : J⁻¹ ∈ W₁ := by
      have := (hgen1 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
    have ht1 : (jp : F) * (J⁻¹) ^ p - 1 ∈ W₁.nonunits := by
      have ht_eq : (jp : F) * (J⁻¹) ^ p - 1 = (J⁻¹) ^ p * ((jp : F) - J ^ p) := by
        rw [mul_sub, ← mul_pow, inv_mul_cancel₀ hj0, one_pow, mul_comm]
      rw [ht_eq]
      refine mul_mem_nonunits_of_mem W₁ (pow_mem hjinv p) ?_
      rw [← hjpeq]; exact ht'
    exact not_mem_nonunits_witness W₁ p J hj0 hj1 hgen1 _ ht1 hs1

end Enum
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

end ModularCurve.DRModel.C4
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel qExpand jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd transcendental_jq DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace DRModel
p2m_export "ModularCurve.DRModel" "exists_chartAlgFin_valuationSubring_pair_levelP isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int"
namespace C4
p2m_open "ModularCurve.DRModel ModularCurve"

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve"

section EnumMain

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull p) : Type)
set_option quotPrecheck false in
local notation "J" => (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))
set_option quotPrecheck false in
local notation "A" => (↥(TwoChartIntegralModel.chartAlgInf ℤ (↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p)) : Type)

theorem mem_iff_dvd_of_qOf_le
    (hH : IsReduced (A ⧸ Ideal.span {((p : ℕ) : A)}) ∧ (Ideal.span {((p : ℕ) : A)}).minimalPrimes.ncard = 2)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hp₀ : ((p : ℕ) : F) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : F) ∈ W₁.nonunits)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits)
    (φ : A →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0)
    (hAW₀ : ∀ a : A, (a : F) ∈ W₀)
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℕ) : A) ∈ 𝔪)
    (hv𝔪 : TwoChartIntegralModel.jInvChartInf ℤ F J ∈ 𝔪) (h0 : qOf W₀ hAW₀ ≤ 𝔪) :
    ∀ a : A, a ∈ 𝔪 ↔ (p : ℤ) ∣ φ a := by
  have hprime : p.Prime := Fact.out
  have hgen0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₀ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₀ :=
    fun P hP => by simpa using hgen 0 P hP
  have hj0 : J ≠ 0 := IgusaScheme.jFull_ne_zero p
  have hjt : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ≠ 0 := by
    intro P hP h0'
    apply transcendental_int_jFull p
    refine ⟨P, fun h => hP (by rw [h, Polynomial.map_zero]), ?_⟩
    rw [Polynomial.aeval_def]; exact h0'
  have h8 := residue_rational_W₀ p jp hjp W₀ W₁ hgen hcomplete ht

  have hpA : ((p : ℤ) : A) ∈ 𝔪 := by simpa using hp𝔪
  have hint𝔪 : ∀ n : ℤ, (n : A) ∈ 𝔪 ↔ (p : ℤ) ∣ n := by
    intro n
    constructor
    · intro hn
      by_contra hnd
      have hcop : IsCoprime (p : ℤ) n := (Nat.prime_iff_prime_int.mp hprime).coprime_iff_not_dvd.mpr hnd
      obtain ⟨c₁, c₂, hcc⟩ := hcop
      apply h𝔪.ne_top
      rw [Ideal.eq_top_iff_one]
      have hmem : (((c₁ * p + c₂ * n : ℤ)) : A) ∈ 𝔪 := by
        push_cast
        exact 𝔪.add_mem (𝔪.mul_mem_left _ hpA) (𝔪.mul_mem_left _ hn)
      rwa [hcc, Int.cast_one] at hmem
    · rintro ⟨k, rfl⟩
      push_cast
      exact 𝔪.mul_mem_right _ hpA
  intro a
  obtain ⟨Pb, hPm, hPb⟩ := exists_bivariate_of_mem_chartAlgInf p a
  obtain ⟨G, hG⟩ := exists_sub_eval₂_mem_nonunits p W₀ J hj0 hp₀ hgen0 hjt h8 (a : F) Pb hPm hPb

  let gA : A := Polynomial.eval₂ (algebraMap ℤ A) (TwoChartIntegralModel.jInvChartInf ℤ F J) G
  have hgA : (gA : F) = Polynomial.eval₂ (algebraMap ℤ F) J⁻¹ G := by
    change (TwoChartIntegralModel.chartAlgInf ℤ F J).val.toRingHom
      (Polynomial.eval₂ (algebraMap ℤ A) (TwoChartIntegralModel.jInvChartInf ℤ F J) G) = _
    rw [Polynomial.hom_eval₂]
    congr 1 <;> exact RingHom.ext_int _ _

  have hsubF : ((a - gA : A) : F) ∈ W₀.nonunits := by
    have : ((a - gA : A) : F) = (a : F) - Polynomial.eval₂ (algebraMap ℤ F) J⁻¹ G := by
      rw [← hgA]; rfl
    rw [this]; exact hG
  have h1 : a - gA ∈ 𝔪 := h0 (mem_qOf.mpr hsubF)

  have h2 : gA - ((G.coeff 0 : ℤ) : A) ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq]
    have hv0 : Ideal.Quotient.mk 𝔪 (TwoChartIntegralModel.jInvChartInf ℤ F J) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hv𝔪
    change Ideal.Quotient.mk 𝔪
      (Polynomial.eval₂ (algebraMap ℤ A) (TwoChartIntegralModel.jInvChartInf ℤ F J) G) = _
    rw [Polynomial.hom_eval₂, hv0, Polynomial.eval₂_at_zero]
    simp
  have h12 : a - ((G.coeff 0 : ℤ) : A) ∈ 𝔪 := by
    have := 𝔪.add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

  have hφv : φ (TwoChartIntegralModel.jInvChartInf ℤ F J) = 0 := phi_jInvChartInf_eq_zero p φ hφ
  have hφg : φ gA = G.coeff 0 := by
    change φ.toRingHom (Polynomial.eval₂ (algebraMap ℤ A) (TwoChartIntegralModel.jInvChartInf ℤ F J) G) = _
    rw [Polynomial.hom_eval₂, show φ.toRingHom (TwoChartIntegralModel.jInvChartInf ℤ F J) = 0 from hφv,
      Polynomial.eval₂_at_zero]
    have hid : φ.toRingHom.comp (algebraMap ℤ A) = RingHom.id ℤ := RingHom.ext_int _ _
    rw [hid]
    rfl
  have hφa : (p : ℤ) ∣ φ a - G.coeff 0 := by
    have := dvd_of_mem_nonunits p hH jp hjp W₀ W₁ hp₀ hp₁ hgen hcomplete ht φ hφ (a - gA) hsubF
    rwa [map_sub, hφg] at this

  have key : a ∈ 𝔪 ↔ ((G.coeff 0 : ℤ) : A) ∈ 𝔪 := by
    constructor
    · intro ha
      have := 𝔪.sub_mem ha h12
      rwa [sub_sub_cancel] at this
    · intro hc
      have := 𝔪.add_mem h12 hc
      rwa [sub_add_cancel] at this
  rw [key, hint𝔪]
  exact (dvd_iff_dvd_of_dvd_sub hφa).symm

theorem enum_main
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ F (IgusaScheme.jFull p)))
    (hjp : ((jp : F) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring F)
    (hp₀ : ((p : ℕ) : F) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : F) ∈ W₁.nonunits)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring F,
        ((p : ℕ) : F) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ F) (IgusaScheme.jFull p : F) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : F) - (IgusaScheme.jFull p : F) ^ p) ∈ W₀.nonunits)
    (φ : A →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : F) : LaurentSeries ℚ).coeff 0) :
    ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ((p : ℕ) : A) ∈ 𝔪 → TwoChartIntegralModel.jInvChartInf ℤ F J ∈ 𝔪 →
      (∀ a : A, a ∈ 𝔪 ↔ (p : ℤ) ∣ φ a) ∨
      ((∀ a : A, (a : F) ∈ W₁.nonunits → a ∈ 𝔪) ∧ (∃ a : A, (a : F) ∈ W₀.nonunits ∧ a ∉ 𝔪)) := by
  intro 𝔪 h𝔪 hp𝔪 hv𝔪
  have hCR := ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int p
  have hH : IsReduced (A ⧸ Ideal.span {((p : ℕ) : A)}) ∧ (Ideal.span {((p : ℕ) : A)}).minimalPrimes.ncard = 2 :=
    ⟨hCR.2.2.1, hCR.2.2.2⟩
  have hgen0 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₀ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₀ :=
    fun P hP => by simpa using hgen 0 P hP
  have hgen1 : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ F) J P ∈ W₁ ∧ (Polynomial.eval₂ (algebraMap ℤ F) J P)⁻¹ ∈ W₁ :=
    fun P hP => by simpa using hgen 1 P hP
  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hu0 : J⁻¹ ∈ W₀ := by have := (hgen0 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
  have hu1 : J⁻¹ ∈ W₁ := by have := (hgen1 Polynomial.X hX).2; rwa [Polynomial.eval₂_X] at this
  have hAW₀ : ∀ a : A, (a : F) ∈ W₀ := coe_mem_of_inv_mem p W₀ hu0
  have hAW₁ : ∀ a : A, (a : F) ∈ W₁ := coe_mem_of_inv_mem p W₁ hu1
  have hinf := inf_qOf_eq_span p hH jp hjp W₀ W₁ hp₀ hp₁ hgen hcomplete ht φ hφ hAW₀ hAW₁
  have hle : qOf W₀ hAW₀ ⊓ qOf W₁ hAW₁ ≤ 𝔪 := by
    rw [hinf]; exact (Ideal.span_singleton_le_iff_mem _).mpr hp𝔪
  by_cases h0 : qOf W₀ hAW₀ ≤ 𝔪
  · exact Or.inl (mem_iff_dvd_of_qOf_le p hH jp hjp W₀ W₁ hp₀ hp₁ hgen hcomplete ht φ hφ hAW₀ 𝔪 h𝔪
      hp𝔪 hv𝔪 h0)
  · right
    have h1 : qOf W₁ hAW₁ ≤ 𝔪 := (h𝔪.isPrime.inf_le.mp hle).resolve_left h0
    refine ⟨fun a ha => h1 (mem_qOf.mpr ha), ?_⟩
    obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.mp h0
    exact ⟨a, mem_qOf.mp ha, hna⟩

end EnumMain
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

end ModularCurve.DRModel.C4
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4 P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve.DRModel.C4.QExp"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime.ModularCurve AlgebraicCurve Polynomial in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (φ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (hφ : ∀ x, ((φ x : ℤ) : ℚ) = ((x : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ).coeff 0) :
    ∀ 𝔪 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      𝔪.IsMaximal →
      ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ∈ 𝔪 →
      TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∈ 𝔪 →
      (∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
          a ∈ 𝔪 ↔ (p : ℤ) ∣ φ a) ∨
      ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
          (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → a ∈ 𝔪) ∧
       (∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
          (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ a ∉ 𝔪)) :=
  ModularCurve.DRModel.C4.enum_main p jp hjp W₀ W₁ hp₀ hp₁ hgen hcomplete ht φ hφ

end S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime
end P2MW
export P2MW.S_ModularCurve_DRModel_forall_mem_iff_dvd_or_forall_mem_of_isMaximal_of_jInvChartInf_mem_of_prime (solution)
