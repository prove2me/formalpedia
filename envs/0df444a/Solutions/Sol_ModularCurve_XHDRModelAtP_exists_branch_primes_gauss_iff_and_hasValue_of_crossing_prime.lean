-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e127825f-ff9e-5c8e-9a6a-99eb33325def

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf
import Theorems.Thm_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
import Theorems.Thm_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace BranchReadReduce

open ModularCurve AlgebraicCurve

def toSubringHom {T F : Type*} [CommRing T] [Field F] (γ : T →+* F) (V : ValuationSubring F) (h : ∀ t, γ t ∈ V) : T →+* ↥V where
  toFun t := ⟨γ t, h t⟩
  map_one' := Subtype.ext (map_one γ)
  map_mul' a b := Subtype.ext (map_mul γ a b)
  map_zero' := Subtype.ext (map_zero γ)
  map_add' a b := Subtype.ext (map_add γ a b)

@[scoped simp] theorem toSubringHom_apply {T F : Type*} [CommRing T] [Field F] (γ : T →+* F) (V : ValuationSubring F) (h : ∀ t, γ t ∈ V) (t : T) :
    toSubringHom γ V h t = ⟨γ t, h t⟩ := rfl

section S3
variable {F T : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {A : ValuationSubring (AlgebraicClosure ℚ)} [CommRing T]

theorem mem_of_fraction (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    (h : F) (a c : T) (hc : c ∉ 𝔯) (hfac : h * γ c = γ a) : h ∈ W := by
  rw [h𝔯def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
  have hc0 : γ c ≠ 0 := by
    intro h0
    apply hc.ne_zero
    exact Subtype.ext h0
  have hh : h = γ a * (γ c)⁻¹ := by rw [← hfac, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  have hinv : ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).1 = (γ c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have hu := congrArg Subtype.val hc.unit.mul_inv
    rw [IsUnit.unit_spec] at hu
    exact hu
  rw [hh, ← hinv]
  exact mul_mem (hγW a) ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).2

theorem regularProlongation_maximalIdeal_iff {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A) Fb]
    (Rg : RegularProlongation A F Fb) (a : ↥A) :
    (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff a).mpr a.2⟩ : ↥Rg.integers) ∈
        IsLocalRing.maximalIdeal ↥Rg.integers ↔ a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [← Rg.ker_residue, RingHom.mem_ker, Rg.residue_algebraMap, map_eq_zero_iff _ (algebraMap (ResidueField ↥A) Fb).injective,
    IsLocalRing.residue_eq_zero_iff]

end S3

theorem natCast_mem_nonunits_integers
    (p : ℕ) [Fact p.Prime] {F Fb : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] [Field Fb]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (ResidueField ↥A) Fb] [CharP (ResidueField ↥A) p]
    (Rg : RegularProlongation A F Fb) :
    (algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ)) ∈ Rg.integers.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨(Rg.algebraMap_mem_iff _).mpr (natCast_mem A p), ?_⟩
  rw [← Rg.ker_residue, RingHom.mem_ker]
  have : (⟨algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr (natCast_mem A p)⟩ : ↥Rg.integers) =
      ⟨algebraMap (AlgebraicClosure ℚ) F (((p : ℕ) : ↥A) : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr ((p : ℕ) : ↥A).2⟩ :=
    Subtype.ext (by simp)
  rw [this, Rg.residue_algebraMap, map_natCast, CharP.cast_eq_zero (ResidueField ↥A) p, map_zero]

theorem finiteType_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) :=
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
    (ModularCurve.translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1

end BranchReadReduce
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime.BranchReadReduce"

open BranchReadReduce in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔔 : 𝔔.IsPrime) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) :
    ∃ (𝔯₀ 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))),
      𝔯₀.IsPrime ∧ 𝔯₁.IsPrime ∧ 𝔯₀ ≤ 𝔔 ∧ 𝔯₁ ≤ 𝔔 ∧ ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ ∧

      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁ ∧

      (∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₀ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)) ∧
      (∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)) ∧

      (∀ (h : ↥(xHFunctionFieldBar M H)) (a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), c ∉ 𝔔 → h * γ c = γ a →
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn0 A hA ρ hρ n).HasValue g (χκ a / χκ c)) ∧
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn1 A hA ρ hρ n).HasValue g (χκ a / χκ c))) := by
  classical

  obtain ⟨Rg, hgauss, hres⟩ :=
    ModularCurve.JHPlaceSpecialization.exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap p M H hpM hpM2 hHp A hA
  obtain ⟨hγG, -⟩ :=
    ModularCurve.XHDRLevel.mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss p M H hpM hj A ρ hρ halg γ hγ Rg hgauss hres
  obtain ⟨hγinj, hγfrac, -⟩ :=
    ModularCurve.XHDRModelAtP.injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
      p M H hpM hj 𝔛 A hA ρ hρ halg (chartAlgFin p (ΓM M H) hj) (ιFin p (ΓM M H) hj)
      (TwoChartIntegralModel.ιFin_toBase _ _ _) 𝔛.Meta_chart_nonempty (fun b => 𝔛.Meta_pin b) γ hγ
  obtain ⟨𝔯₀, h𝔯₀def⟩ : ∃ 𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers :=
    ⟨(IsLocalRing.maximalIdeal ↥Rg.integers).comap (toSubringHom γ Rg.integers hγG), fun t => Iff.rfl⟩
  haveI h𝔯₀p : 𝔯₀.IsPrime := by
    have : 𝔯₀ = (IsLocalRing.maximalIdeal ↥Rg.integers).comap (toSubringHom γ Rg.integers hγG) := by
      ext t; exact h𝔯₀def t
    rw [this]
    exact Ideal.comap_isPrime _ _

  obtain ⟨𝔯₁, h𝔯₁p, hle₀, hle₁, hnc₀₁, hnc₁₀, hb, hc₁, hmin₀⟩ :=
    ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ hwgen γ hγ n 𝔔 h𝔔 χκ hker hχA ht
      Rg hgauss hres hγG hγinj hγfrac 𝔯₀ h𝔯₀def

  haveI : Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) := finiteType_chartAlgFin p M H hj
  haveI : Module.Flat (R p) ↥(chartAlgFin p (ΓM M H) hj) := (ModularCurve.XHDRLevel.flat_chartAlgFin_and_flat_chartAlgInf p (ΓM M H) hj).1
  have hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
    intro a
    apply Subtype.ext
    show ((γ (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hγ, OneMemClass.coe_one, OneMemClass.coe_one, map_one, ← HahnSeries.C_mul_eq_smul, mul_one,
      show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) from rfl,
      ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  have hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rg.integers := fun a =>
    (Rg.algebraMap_mem_iff _).mpr a.2
  have hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA a⟩ : ↥Rg.integers) ∈
      IsLocalRing.maximalIdeal ↥Rg.integers ↔ a ∈ IsLocalRing.maximalIdeal ↥A := fun a => regularProlongation_maximalIdeal_iff Rg a
  have hpW := natCast_mem_nonunits_integers p A Rg
  have hc₀ : ∀ h : ↥(xHFunctionFieldBar M H), (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₀ ∧ h * γ c = γ a) ↔
      (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) := by
    intro h
    rw [← hgauss]
    constructor
    · rintro ⟨a, c, hc, hfac⟩
      exact mem_of_fraction Rg.integers γ hγG 𝔯₀ h𝔯₀def h a c hc hfac
    · intro hh
      exact ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
        p M H hpM A hA ρ hρ halg ↥(chartAlgFin p (ΓM M H) hj) Rg.integers γ hγG hγinj hγfrac hγA hWA hW𝔪 hpW 𝔯₀ h𝔯₀def hmin₀ h hh

  have he := ModularCurve.XHDRModelAtP.hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ hwgen γ hγ hγinj n 𝔔 χκ hker hχA ht
  exact ⟨𝔯₀, 𝔯₁, h𝔯₀p, h𝔯₁p, hle₀, hle₁, hnc₀₁, hnc₁₀, hb, hc₀, hc₁, he⟩

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime.BranchReadReduce"

end S_ModularCurve_XHDRModelAtP_exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime (solution)
