-- Prove2me | solution 1 for ModularCurve.isKummerGenerator_one_hasseRootFn_of_charP_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/86214c51-d76c-549b-887d-156498d397da

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isKummerGenerator_one_hasseRootFn_of_charP_two
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq"
p2m_attr_erase "simp" "GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma

namespace KG2Aux

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ (Δ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem isIntegralQExp_pow {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) {k : ℤ}
    (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (n : ℕ) : IsIntegralQExp (f.pow n) (pf ^ n) := by
  rw [IsIntegralQExp, map_pow, hf]
  exact (ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods hT) f n).symm

theorem isIntegralQExp_mul {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) {a b : ℤ}
    (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) a) (g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) b)
    {s t : PowerSeries ℤ} (hf : IsIntegralQExp f s) (hg : IsIntegralQExp g t) : IsIntegralQExp (f.mul g) (s * t) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [map_mul, hf, hg, ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods hT)]

theorem isIntegralQExp_mcast {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : ℤ} (h : a = b) (f : ModularForm Γ a)
    {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) : IsIntegralQExp (ModularForm.mcast h f) pf := by
  rw [IsIntegralQExp, ModularForm.coe_mcast]
  exact hf

theorem intSeriesC_pow (K : Type*) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  simp [intSeriesC]

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num)]
  norm_num [Nat.choose]

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]

noncomputable def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

noncomputable def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

theorem isIntegralQExp_E4 : IsIntegralQExp (⇑ModularForm.E₄ : UpperHalfPlane → ℂ) e4Z := by
  rw [isIntegralQExp_iff]
  intro n
  have h := EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 4) (by decide : Even 4) n
  rw [ModularForm.E₄] at *
  rw [h]
  simp only [e4Z, PowerSeries.coeff_mk]
  split_ifs with hn
  · simp
  · rw [bernoulli_four]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (⇑ModularForm.E₆ : UpperHalfPlane → ℂ) e6Z := by
  rw [isIntegralQExp_iff]
  intro n
  have h := EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 6) (by decide : Even 6) n
  rw [h]
  simp only [e6Z, PowerSeries.coeff_mk]
  split_ifs with hn
  · simp
  · rw [bernoulli_six]
    push_cast
    ring

theorem intSeriesC_e4Z (κ : Type*) [Field κ] [CharP κ 2] : intSeriesC κ e4Z = 1 := by
  have hmap : e4Z.map (Int.castRingHom κ) = 1 := by
    ext n
    rw [PowerSeries.coeff_map, e4Z, PowerSeries.coeff_mk, PowerSeries.coeff_one, eq_intCast]
    split_ifs with hn
    · simp
    · rw [show (240 : ℤ) * (σ 3 n : ℤ) = 2 * (120 * (σ 3 n : ℤ)) by ring, Int.cast_mul,
        show ((2 : ℤ) : κ) = 0 from (CharP.intCast_eq_zero_iff κ 2 2).2 (dvd_refl 2), zero_mul]
  simp [intSeriesC, hmap]

theorem intSeriesC_e6Z (κ : Type*) [Field κ] [CharP κ 2] : intSeriesC κ e6Z = 1 := by
  have hmap : e6Z.map (Int.castRingHom κ) = 1 := by
    ext n
    rw [PowerSeries.coeff_map, e6Z, PowerSeries.coeff_mk, PowerSeries.coeff_one, eq_intCast]
    split_ifs with hn
    · simp
    · rw [show (-504 : ℤ) * (σ 5 n : ℤ) = 2 * (-252 * (σ 5 n : ℤ)) by ring, Int.cast_mul,
        show ((2 : ℤ) : κ) = 0 from (CharP.intCast_eq_zero_iff κ 2 2).2 (dvd_refl 2), zero_mul]
  simp [intSeriesC, hmap]

end KG2Aux

open KG2Aux in

theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (h2M : ¬ 2 ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k 2]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ModularCurve.IgusaCover.IsKummerGenerator 1 (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn := by
  refine ⟨by norm_num, w.hasseRootFn_ne_zero, ?_⟩
  rw [pow_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ModularCurve.mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC 2 M hM h2M k

  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
    Subgroup.map_le_range _ _

  let E6' : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 6 := restrictForm hle ModularForm.E₆
  let E4' : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 4 := restrictForm hle ModularForm.E₄
  have hE6 : IsIntegralQExp E6' e6Z := isIntegralQExp_E6
  have hE4 : IsIntegralQExp E4' e4Z := isIntegralQExp_E4

  have hwt : ((2 : ℕ) : ℤ) * 1 + 4 = 6 := by norm_num
  let g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 6 :=
    ModularForm.mcast hwt ((w.form.pow 2).mul E4')
  have hg : IsIntegralQExp g (w.series ^ 2 * e4Z) :=
    isIntegralQExp_mcast hwt _
      (isIntegralQExp_mul (T_mem_Gamma1 M) _ _ (isIntegralQExp_pow (T_mem_Gamma1 M) w.form w.isIntegralQExp 2) hE4)
  have hg0 : intSeriesC k (w.series ^ 2 * e4Z) ≠ 0 := by
    rw [intSeriesC_mul, intSeriesC_pow, intSeriesC_e4Z, mul_one]
    exact pow_ne_zero _ w.intSeriesC_ne_zero
  have key : w.hasseRootFn ^ 2 = intSeriesC k e6Z / intSeriesC k (w.series ^ 2 * e4Z) := by
    rw [intSeriesC_e6Z, intSeriesC_mul, intSeriesC_pow, intSeriesC_e4Z, mul_one, one_div,
      IntegralWeightOneForm.hasseRootFn, inv_pow]
  rw [key]
  exact div_mem_qExpFunctionFieldC E6' g hE6 hg hg0

#print axioms solution

end S_ModularCurve_isKummerGenerator_one_hasseRootFn_of_charP_two
end P2MW
export P2MW.S_ModularCurve_isKummerGenerator_one_hasseRootFn_of_charP_two (solution)
