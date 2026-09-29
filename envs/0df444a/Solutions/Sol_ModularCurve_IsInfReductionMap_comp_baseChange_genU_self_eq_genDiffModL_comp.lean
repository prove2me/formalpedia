-- Prove2me | solution 1 for ModularCurve.IsInfReductionMap.comp_baseChange_genU_self_eq_genDiffModL_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/57d7341a-3b9d-565b-98b4-f0b604866a74

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups
open ModularCurve

namespace C4Main

noncomputable def decimate (p : ℕ) (pf : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n * p) pf

theorem isIntegralQExp_heckeULinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (p : ℕ) (hp : p.Prime) (hpM : p ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (pf : PowerSeries ℤ) (hf : IsIntegralQExp ⇑f pf) :
    IsIntegralQExp ⇑(CuspForm.heckeULinH 2 p f) (decimate p pf) := by
  rw [isIntegralQExp_iff]
  intro n
  have hU := CuspForm.stableU M H 2 hp hpM
  have hΓ : (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
    exact AddSubgroup.mem_zmultiples _
  have h1 : PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑(CuspForm.heckeULinH 2 p f)) =
      ModularFormClass.qCoeff ⇑(CuspForm.heckeULinH 2 p f) n := rfl
  rw [decimate, PowerSeries.coeff_mk, h1, CuspForm.coe_heckeULinH_apply 2 hU,
    ModularFormClass.qCoeff_heckeU f hΓ hp.ne_zero n, ModularForm.coeffHeckeU_apply]
  exact hf.coeff (n * p)

theorem intSeriesC_decimate (K : Type*) [Field K] (p : ℕ) [NeZero p] (pf : PowerSeries ℤ) :
    intSeriesC K (decimate p pf) = qDecimate K p (intSeriesC K pf) := by
  ext k
  rw [coeff_qDecimate]
  rcases lt_or_ge k 0 with hk | hk
  · have hpk : (p : ℤ) * k < 0 := by
      have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
      nlinarith
    rw [intSeriesC, intSeriesC, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hpk]
  · lift k to ℕ using hk with n
    have hpn : ((p : ℤ) * (n : ℤ)) = ((n * p : ℕ) : ℤ) := by push_cast; ring
    rw [hpn, intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_map, decimate, PowerSeries.coeff_mk]

theorem closure_integral_eq_top (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) :
    AddSubgroup.closure {x : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) |
        (x : CuspForm (CohCarrier.GammaH M H) 2) ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Submodule.span_induction with
  | mem y hy => exact AddSubgroup.subset_closure hy
  | zero => exact AddSubgroup.zero_mem _
  | add y z hy hz ihy ihz => exact AddSubgroup.add_mem _ ihy ihz
  | smul a y hy ih =>
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have : (⟨a • y, Submodule.smul_mem _ a hy⟩ : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) =
        n • ⟨y, hy⟩ := by
      apply Subtype.ext
      show a • y = ((n • (⟨y, hy⟩ : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
        CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) : CuspForm (CohCarrier.GammaH M H) 2)
      rw [Submodule.coe_smul_of_tower]
      show (a : ℂ) • y = n • y
      rw [← hn, Int.cast_smul_eq_zsmul]
    rw [this]
    exact AddSubgroup.zsmul_mem _ ih n

end C4Main

open C4Main in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K] (S : Set ℕ)
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ) :
    ρ ∘ₗ (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.U p Fact.out hpM)).baseChange K =
      ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ∘ₗ ρ := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI hMp : NeZero (M / p) := ModularCurve.neZero_div p M hpM

  rw [ModularCurve.genDiffModL_U_self]
  have hC : IsFrobPushDiff K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p
      (frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) :=
    isFrobPushDiff_frobPushDiffModL
      (ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH p K (M / p) (infSubgroup p M H hpM))

  have hΘ : Function.Injective (diffQExp (qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) :=
    ModularCurve.diffQExp_qExpFunctionFieldC_injective K _ (ModularCurve.translation_mem_GammaH (M / p) _)

  obtain ⟨W⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hp hpM hpM2
  have hint : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) →
      ∃ pf : PowerSeries ℤ, IsIntegralQExp ⇑f pf := by
    intro f hf
    have hc : ∀ n : ℕ, ModularFormClass.qCoeff ⇑f n ∈ (⊥ : Subring ℂ) := fun n =>
      (by simpa using (hf 1 (Subring.one_mem _) W n).1)
    choose a ha using fun n => Subring.mem_bot.mp (hc n)
    refine ⟨PowerSeries.mk a, ?_⟩
    rw [isIntegralQExp_iff]
    intro n
    rw [PowerSeries.coeff_mk, ha n]
    rfl

  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k m => ?_
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
  have e : ∀ x : CuspForm.IntTwoCuspForms M H p,
      (k ⊗ₜ[ZMod p] x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) = k • ((1 : K) ⊗ₜ[ZMod p] x) := fun x => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, e m, map_smul, map_smul, map_smul]
  congr 1

  obtain ⟨x, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p m
  let A : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) →+
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] :=
    { toFun := fun x => ρ ((1 : K) ⊗ₜ[ZMod p]
        (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.U p Fact.out hpM) (CuspForm.intTwoCuspReduce M H p x)))
      map_zero' := by simp only [map_zero, TensorProduct.tmul_zero]
      map_add' := fun x y => by simp only [map_add, TensorProduct.tmul_add] }
  let B : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) →+
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] :=
    { toFun := fun x => frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p
        (ρ ((1 : K) ⊗ₜ[ZMod p] (CuspForm.intTwoCuspReduce M H p x)))
      map_zero' := by simp only [map_zero, TensorProduct.tmul_zero]
      map_add' := fun x y => by simp only [map_add, TensorProduct.tmul_add] }
  suffices hAB : Set.EqOn A B {x : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) |
      (x : CuspForm (CohCarrier.GammaH M H) 2) ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)} by
    have hx : x ∈ AddSubgroup.closure {x : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) |
        (x : CuspForm (CohCarrier.GammaH M H) 2) ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)} := by
      rw [closure_integral_eq_top]; trivial
    exact AddMonoidHom.eqOn_closure hAB hx
  rintro ⟨f, hfL⟩ hf
  obtain ⟨pf, hpf⟩ := hint f hf
  have hUf : CuspForm.heckeULinH 2 p f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet
      (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.U p Fact.out hpM)) hf
  have hA : diffQExp _ (A ⟨f, hfL⟩) = intSeriesC K (decimate p pf) := by
    show diffQExp _ (ρ ((1 : K) ⊗ₜ[ZMod p] (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.U p Fact.out hpM)
      (CuspForm.intTwoCuspReduce M H p ⟨f, hfL⟩)))) = _
    rw [CuspForm.intTwoCuspGenMod_reduce]
    exact hρ.diffQExp_apply hUf (isIntegralQExp_heckeULinH p hp hpM f pf hpf)
  have hB : diffQExp _ (B ⟨f, hfL⟩) = qDecimate K p (intSeriesC K pf) := by
    show diffQExp _ (frobPushDiffModL K _ p (ρ ((1 : K) ⊗ₜ[ZMod p] (CuspForm.intTwoCuspReduce M H p ⟨f, hfL⟩)))) = _
    rw [hC]
    congr 1
    exact hρ.diffQExp_apply hf hpf
  apply hΘ
  rw [hA, hB, intSeriesC_decimate]

end S_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp
end P2MW
export P2MW.S_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp (solution)
