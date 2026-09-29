-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_levelPolynomials_of_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8400d322-c73d-5671-be0e-0eff7954f576

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval
import Theorems.Thm_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
import Theorems.Thm_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_levelPolynomials_of_chartAlgFin
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian"
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace SNearAlg

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

private def toZ (q : ℕ) [Fact q.Prime] : R q →+* ZMod q :=
  have hq : (q : ℕ).Prime := Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (g := Int.castRingHom (ZMod q)) (fun y => by
    rw [isUnit_iff_ne_zero, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := y.2
    rwa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] at this)

private theorem toZ_comp_algebraMap (q : ℕ) [Fact q.Prime] : (toZ q).comp (algebraMap ℤ (R q)) = Int.castRingHom (ZMod q) :=
  RingHom.ext_int _ _

private theorem isCoprime_map_of_monic (q : ℕ) [Fact q.Prime] (p₁ p₂ : ℤ[X]) (h₁ : p₁.Monic)
    (h : IsCoprime (p₁.map (Int.castRingHom (ZMod q))) (p₂.map (Int.castRingHom (ZMod q)))) :
    IsCoprime (p₁.map (algebraMap ℤ (R q))) (p₂.map (algebraMap ℤ (R q))) := by
  have hq : (q : ℕ).Prime := Fact.out
  haveI : IsLocalRing (R q) := GaloisRep.ratLocalizedAt.isLocalRing hq
  refine Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker (toZ q) ?_ _ _ (h₁.map _) ?_
  · rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_natCast]
    exact ZMod.natCast_self q
  · rwa [Polynomial.map_map, Polynomial.map_map, toZ_comp_algebraMap]

private theorem sup_span_aeval_eq_top {T S : Type*} [CommRing T] [CommRing S] [Algebra T S] (x : S) {f g : T[X]}
    (h : IsCoprime f g) : Ideal.span {aeval x f} ⊔ Ideal.span {aeval x g} = (⊤ : Ideal S) := by
  obtain ⟨a, b, hab⟩ := h
  rw [Ideal.eq_top_iff_one]
  have : (1 : S) = aeval x a * aeval x f + aeval x b * aeval x g := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

private theorem sup_span_aeval_eq_top_int (q : ℕ) [Fact q.Prime] {S : Type*} [CommRing S] [Algebra (R q) S] (x : S) (p₁ p₂ : ℤ[X]) (h₁ : p₁.Monic)
    (h : IsCoprime (p₁.map (Int.castRingHom (ZMod q))) (p₂.map (Int.castRingHom (ZMod q)))) :
    Ideal.span {aeval x p₁} ⊔ Ideal.span {aeval x p₂} = (⊤ : Ideal S) := by
  have := sup_span_aeval_eq_top x (isCoprime_map_of_monic q p₁ p₂ h₁ h)
  rwa [Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap] at this

private def twist (q : ℕ) (g : ℤ[X]) (D : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (D + 1), C (g.coeff k * (q : ℤ) ^ (12 * k)) * Polynomial.X ^ (D - k)

private theorem twist_map (q : ℕ) (g : ℤ[X]) (D : ℕ) (hq : (q : ZMod q) = 0) :
    (twist q g D).map (Int.castRingHom (ZMod q)) = C ((g.map (Int.castRingHom (ZMod q))).coeff 0) * Polynomial.X ^ D := by
  rw [twist, Polynomial.map_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Polynomial.map_mul, Polynomial.map_pow]
  · intro k _
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hq,
      zero_pow (by omega), mul_zero, C_0, zero_mul]

private theorem aeval_twist (q : ℕ) {S : Type*} [CommRing S] (v v' : S) (hvv' : v * v' = (q : S) ^ 12)
    (g : ℤ[X]) (D : ℕ) (hD : g.natDegree ≤ D) :
    aeval v (twist q g D) = v ^ D * aeval v' g := by
  rw [twist, map_sum, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hD) v', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, aeval_X, aeval_C, zsmul_eq_mul, map_mul, eq_intCast, eq_intCast, Int.cast_pow, Int.cast_natCast]

  have : (q : S) ^ (12 * k) * v ^ (D - k) = v ^ D * v' ^ k := by
    rw [pow_mul, ← hvv', mul_pow]
    calc v ^ k * v' ^ k * v ^ (D - k) = (v ^ k * v ^ (D - k)) * v' ^ k := by ring
      _ = v ^ D * v' ^ k := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [mul_assoc, this]
  ring

end SNearAlg

end

open SNearAlg _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in
open ModularCurve.DRModelPackageLevel in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹)
    (v' : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hvv' : v * v' = (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ^ 12)
    (A₀ B₀ n₀ : ℕ) :
    ∃ (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M) (g : Fin M → ℤ[X]) (rk : Fin M → ℕ),
      (∀ i, (g i).Monic) ∧
      (∀ i, Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧
        Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i) ∧
      (∀ i, 1 ≤ rk i) ∧ (∀ i, rk i ≤ b) ∧
      (Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ∧
      (∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v' (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ∧
      (∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) := by
  classical
  have hq : (q : ℕ).Prime := Fact.out

  obtain ⟨avoid, havoid, c₀, hc₀, K, hN2⟩ := exists_finite_etale_quotient_span_aeval N₀ q hqN 𝔓 v hv

  obtain ⟨D, M, g, hD2, hDN, hM, hmon, hirr, -, hcop, hav, h0⟩ :=
    Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime q n₀ A₀ B₀ K (c₀.natDegree + 1) avoid havoid
  have hndvd : ∀ i, ¬ g i ∣ c₀ := fun i hdvd => by
    have := Polynomial.natDegree_le_of_dvd hdvd hc₀
    rw [(hmon i).2] at this
    omega
  have hdeg1 : ∀ i, 1 ≤ (g i).natDegree := fun i => by rw [(hmon i).2]; omega
  have hB := fun i => hN2 (g i) (hmon i).1 (hdeg1 i) (hirr i) (hav i) (hndvd i)
  haveI hfin : ∀ i, Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).1
  haveI het : ∀ i, Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).2.1
  haveI hfree : ∀ i, Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) := fun i => (hB i).2.2.1

  have hX : ∀ i, IsCoprime ((g i).map (Int.castRingHom (ZMod q))) Polynomial.X := by
    intro i
    refine isCoprime_comm.mp ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr ?_)
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h0 i
  refine ⟨K * D, M, hM, g, fun i => Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}), fun i => (hmon i).1,
    fun i => ⟨hfin i, het i, hfree i, rfl⟩, fun i => (hB i).2.2.2.1, fun i => ?_, ?_, ?_, ?_⟩
  ·
    have := (hB i).2.2.2.2
    rwa [(hmon i).2] at this
  ·
    intro i j hij
    exact sup_span_aeval_eq_top_int q v (g i) (g j) (hmon i).1 (hcop i j hij)
  ·
    intro i j
    have hqA : (q : ZMod q) = 0 := ZMod.natCast_self q
    have hcop' : IsCoprime ((g i).map (Int.castRingHom (ZMod q))) ((twist q (g j) D).map (Int.castRingHom (ZMod q))) := by
      rw [twist_map q (g j) D hqA]
      refine (isCoprime_mul_unit_left_right ?_ _ _).mpr ((hX i).pow_right)
      refine isUnit_C.mpr (IsUnit.mk0 _ ?_)
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact h0 j
    have htop := sup_span_aeval_eq_top_int q v (g i) (twist q (g j) D) (hmon i).1 hcop'
    have hvv'A : (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) * v' = ((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ^ 12 := hvv'
    rw [aeval_twist q v v' hvv'A (g j) D (le_of_eq (hmon j).2)] at htop

    refine top_le_iff.mp (htop.symm.le.trans (sup_le_sup_left ?_ _))
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  ·
    intro i
    have := sup_span_aeval_eq_top_int q v (g i) Polynomial.X (hmon i).1 (by rw [Polynomial.map_X]; exact hX i)
    rwa [aeval_X] at this

end S_ModularCurve_DRModelPackageLevel_exists_levelPolynomials_of_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_levelPolynomials_of_chartAlgFin (solution)
