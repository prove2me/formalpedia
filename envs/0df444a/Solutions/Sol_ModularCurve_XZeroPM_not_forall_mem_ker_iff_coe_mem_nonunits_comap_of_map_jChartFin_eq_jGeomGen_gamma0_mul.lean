-- Prove2me | solution 1 for ModularCurve.XZeroPM.not_forall_mem_ker_iff_coe_mem_nonunits_comap_of_map_jChartFin_eq_jGeomGen_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3860b26c-aa31-5781-92c3-49e5d482f112

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
import Theorems.Thm_ModularCurve_forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroPM_not_forall_mem_ker_iff_coe_mem_nonunits_comap_of_map_jChartFin_eq_jGeomGen_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace FrobObstr

theorem mem_nonunits_comap_iff {K K' : Type*} [Field K] [Field K'] (V : ValuationSubring K') (f : K →+* K') (x : K) :
    x ∈ (V.comap f).nonunits ↔ f x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero, ← map_inv₀]
  rfl

theorem mul_mem_nonunits {K : Type*} [Field K] (V : ValuationSubring K) {x y : K} (hx : x ∈ V) (hy : y ∈ V.nonunits) :
    x * y ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hy ⊢
  rw [map_mul]
  have hx' : V.valuation x ≤ 1 := (V.valuation_le_one_iff x).mpr hx
  calc V.valuation x * V.valuation y ≤ 1 * V.valuation y := mul_le_mul_left hx' _
    _ = V.valuation y := one_mul _
    _ < 1 := hy

end FrobObstr

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    [NeZero p]
    (W₀ : ValuationSubring ↥K₂)
    (hW₀ : ∀ f : ↥K₂, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (σ : ↥K₂ ≃ₐ[L] ↥K₂)
    (hσj : ((σ j₂ : ↥K₂) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hρϖ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0)
    (hρj : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen k M) :
    ¬ (∀ b : ↥(chartAlgFin A (↥K₂) j₂), b ∈ RingHom.ker ρ ↔ ((b : ↥K₂)) ∈ (W₀.comap (σ : ↥K₂ ≃ₐ[L] ↥K₂).toAlgHom.toRingHom).nonunits) := by
  classical
  intro hker
  have hp : p.Prime := Fact.out
  set W₁ : ValuationSubring ↥K₂ := W₀.comap (σ : ↥K₂ ≃ₐ[L] ↥K₂).toAlgHom.toRingHom with hW₁

  obtain ⟨hjW₀, hcong⟩ := ModularCurve.map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand p L K₂ A hAp j₂ hj₂ W₀ hW₀ σ hσj
  obtain ⟨hVA, hVm, hVj⟩ := ModularCurve.forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand
    p L K₂ A hAp j₂ hj₂ W₀ hW₀ σ hσj

  have htj : Transcendental A j₂ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₂ A j₂ hj₂
  have hj₂' : ((j₂ : ↥K₂) : LaurentSeries L) = ModularCurve.jqModC L := by
    rw [hj₂]; exact ModularCurve.map_jqModC (algebraMap ℚ L)
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := by
    subst hK₂
    haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
    have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]
    exact (ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      L (CongruenceSubgroup.Gamma0 (M * p)) hT0 j₂ hj₂').2
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := inferInstance
  obtain ⟨hle, ⟨𝔓, h𝔓p, h𝔓1, h𝔓mem, h𝔓A, hloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₂) j₂ htj hFD hsep W₁ hVA hVm hVj

  have ht : σ.symm j₂ ∈ W₁ := by
    show (σ : ↥K₂ ≃ₐ[L] ↥K₂).toAlgHom.toRingHom (σ.symm j₂) ∈ W₀
    change σ (σ.symm j₂) ∈ W₀
    rw [AlgEquiv.apply_symm_apply]; exact hjW₀
  obtain ⟨a, b, hb𝔓, htba⟩ := (hloc (σ.symm j₂)).1 ht
  have hdiff : (j₂ : ↥K₂) - (σ.symm j₂) ^ p ∈ W₁.nonunits := by
    rw [hW₁, FrobObstr.mem_nonunits_comap_iff]
    change σ (j₂ - σ.symm j₂ ^ p) ∈ W₀.nonunits
    rw [map_sub, map_pow, AlgEquiv.apply_symm_apply]; exact hcong

  have hbW : ((b : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) ∈ W₁ := hle b
  have helt : ((jChartFin A (↥K₂) j₂ * b ^ p - a ^ p : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) ∈ W₁.nonunits := by
    have hcoe : ((jChartFin A (↥K₂) j₂ * b ^ p - a ^ p : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) =
        ((b : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) ^ p * ((j₂ : ↥K₂) - (σ.symm j₂) ^ p) := by
      have hj : ((jChartFin A (↥K₂) j₂ : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) = j₂ := rfl
      push_cast
      rw [hj, ← htba]; ring
    rw [hcoe]
    exact FrobObstr.mul_mem_nonunits W₁ (pow_mem hbW p) hdiff

  have hk1 : (jChartFin A (↥K₂) j₂ * b ^ p - a ^ p : ↥(chartAlgFin A (↥K₂) j₂)) ∈ RingHom.ker ρ := (hker _).2 helt
  have hk2 : b ∉ RingHom.ker ρ := fun h => hb𝔓 ((h𝔓mem b).2 ((hker b).1 h))
  have hk1' : ρ (jChartFin A (↥K₂) j₂) * ρ b ^ p = ρ a ^ p := by
    have h := hk1
    rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow] at h
    exact sub_eq_zero.mp h
  rw [hρj] at hk1'
  rw [RingHom.mem_ker] at hk2

  have hcoeq : (ModularCurve.jqModC k) * (((ρ b : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)) ^ p =
      (((ρ a : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)) ^ p := by
    have := congrArg (fun z : ↥(ModularCurve.modularFunctionFieldC k M) => (z : LaurentSeries k)) hk1'
    simpa using this
  have hb0 : (((ρ b : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)) ≠ 0 := by
    intro h; apply hk2; exact_mod_cast h
  have hj0 : ModularCurve.jqModC k ≠ 0 := by
    intro h; have := ModularCurve.order_jqModC_def k; rw [h, HahnSeries.order_zero] at this; exact absurd this (by norm_num)
  have ha0 : (((ρ a : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)) ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero, mul_eq_zero] at hcoeq
    rcases hcoeq with h1 | h1
    · exact hj0 h1
    · exact hb0 (pow_eq_zero_iff hp.ne_zero |>.mp h1)
  have hord := congrArg HahnSeries.order hcoeq
  rw [HahnSeries.order_mul hj0 (pow_ne_zero p hb0), HahnSeries.order_pow, HahnSeries.order_pow,
    ModularCurve.order_jqModC_def] at hord

  have hdvd : (p : ℤ) ∣ 1 := by
    refine ⟨(((ρ b : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)).order -
      (((ρ a : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k)).order, ?_⟩
    rw [nsmul_eq_mul, nsmul_eq_mul] at hord
    linear_combination (-1 : ℤ) * hord
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have := hp.two_le
  omega

#print axioms solution

end S_ModularCurve_XZeroPM_not_forall_mem_ker_iff_coe_mem_nonunits_comap_of_map_jChartFin_eq_jGeomGen_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroPM_not_forall_mem_ker_iff_coe_mem_nonunits_comap_of_map_jChartFin_eq_jGeomGen_gamma0_mul (solution)
