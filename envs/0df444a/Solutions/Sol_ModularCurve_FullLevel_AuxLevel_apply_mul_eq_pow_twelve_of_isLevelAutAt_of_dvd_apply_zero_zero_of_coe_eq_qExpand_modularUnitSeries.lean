-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/cf368c88-e14f-565a-8e43-20ec9354b7d3

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix
import Theorems.Thm_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel
open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold Pointwise

namespace OggPres

noncomputable def DeltaMF : ModularForm 𝒮ℒ 12 where
  toFun := ModularForm.discriminant
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq CuspForm.discriminant γ hγ
  holo' := ModularFormClass.holo CuspForm.discriminant
  bdd_at_cusps' := fun hc γ hγ => ModularFormClass.bdd_at_cusps CuspForm.discriminant hc γ hγ

@[scoped simp] theorem coe_DeltaMF : (⇑DeltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem gamma_le_SL (N : ℕ) :
    ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  rintro g ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

noncomputable def DeltaG (N : ℕ) :
    ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  ModularCurve.restrictForm (gamma_le_SL N) DeltaMF

@[scoped simp] theorem coe_DeltaG (N : ℕ) : (⇑(DeltaG N) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem mapGL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe]

def conjLift (d : ℕ) (γ : SL(2, ℤ)) (h : (d : ℤ) ∣ (γ 1 0 : ℤ)) (hd : d ≠ 0) : SL(2, ℤ) :=
  ⟨!![(γ 0 0 : ℤ), (d : ℤ) * (γ 0 1 : ℤ); (γ 1 0 : ℤ) / (d : ℤ), (γ 1 1 : ℤ)], by
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    obtain ⟨c, hc⟩ := h
    rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hd)]
    rw [hc] at hdet
    linear_combination hdet⟩

theorem heckeDiag_mul_coe_eq (d : ℕ) (hd : d ≠ 0) (γ : SL(2, ℤ)) (h : (d : ℤ) ∣ (γ 1 0 : ℤ)) :
    ModularForm.heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjLift d γ h hd) * ModularForm.heckeDiagMatrix d := by
  obtain ⟨c, hc⟩ := h
  have hcd : ((γ 1 0 : ℤ) / (d : ℤ) : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hd)]
  have e00 : ((conjLift d γ ⟨c, hc⟩ hd : SL(2, ℤ)) 0 0 : ℤ) = γ 0 0 := rfl
  have e01 : ((conjLift d γ ⟨c, hc⟩ hd : SL(2, ℤ)) 0 1 : ℤ) = d * γ 0 1 := rfl
  have e10 : ((conjLift d γ ⟨c, hc⟩ hd : SL(2, ℤ)) 1 0 : ℤ) = c := hcd
  have e11 : ((conjLift d γ ⟨c, hc⟩ hd : SL(2, ℤ)) 1 1 : ℤ) = γ 1 1 := rfl
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hd, mapGL_apply]
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, hc] <;> push_cast <;> ring

theorem gamma_le_conj (d N : ℕ) (hd : d ≠ 0) (hdN : d ∣ N) :
    ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (ModularForm.heckeDiagMatrix d)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  rintro g ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  have hγ10 : (d : ℤ) ∣ (γ 1 0 : ℤ) := by
    have := CongruenceSubgroup.Gamma_mem.mp hγ
    obtain ⟨-, -, h10, -⟩ := this
    have : (N : ℤ) ∣ (γ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h10
    exact (Int.natCast_dvd_natCast.mpr hdN).trans this
  refine ⟨conjLift d γ hγ10 hd, ?_⟩
  rw [eq_mul_inv_iff_mul_eq, heckeDiag_mul_coe_eq d hd γ hγ10]

noncomputable def DeltaTG (d N : ℕ) (hd : d ≠ 0) (hdN : d ∣ N) :
    ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  ModularCurve.restrictForm (gamma_le_conj d N hd hdN) (ModularForm.translate DeltaMF (ModularForm.heckeDiagMatrix d))

@[scoped simp] theorem coe_DeltaTG (d N : ℕ) (hd : d ≠ 0) (hdN : d ∣ N) :
    (⇑(DeltaTG d N hd hdN) : ℍ → ℂ) = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d := rfl

theorem delta_slash_SL (ρ : SL(2, ℤ)) :
    ModularForm.discriminant ∣[(12 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ ρ) = ModularForm.discriminant := by
  have := SlashInvariantFormClass.slash_action_eq CuspForm.discriminant (Matrix.SpecialLinearGroup.mapGL ℝ ρ) ⟨ρ, rfl⟩
  simpa only [CuspForm.coe_discriminant] using this

theorem deltaT_slash_of_dvd (d : ℕ) (hd : d ≠ 0) (ρ : SL(2, ℤ)) (h : (d : ℤ) ∣ (ρ 1 0 : ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d) ∣[(12 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ ρ) =
      ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d := by
  rw [← SlashAction.slash_mul, heckeDiag_mul_coe_eq d hd ρ h, SlashAction.slash_mul, delta_slash_SL]

theorem one_mem_strictPeriods_conj (d : ℕ) (hd : d ≠ 0) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (ModularForm.heckeDiagMatrix d)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨ModularGroup.T ^ (d : ℤ), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  have hT : ∀ i j : Fin 2, ((ModularGroup.T ^ (d : ℤ) : SL(2, ℤ)) i j : ℤ) = !![(1 : ℤ), d; 0, 1] i j := by
    intro i j; rw [ModularGroup.coe_T_zpow]
  have hU : ((Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1] := by
    simp [Matrix.GeneralLinearGroup.upperRightHom]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hd, mapGL_apply, hT, hU]
  fin_cases i <;> fin_cases j <;> simp

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_SL2Z]; exact AddSubgroup.mem_zmultiples (1 : ℝ)

theorem coe_eq_mapGL (ρ : SL(2, ℤ)) : ((ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ ρ := rfl

noncomputable def dX : PowerSeries ℤ := PowerSeries.X * ModularCurve.dedekindEtaUnit

theorem qExpansion_one_delta :
    qExpansion 1 ModularForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) dX :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

theorem coeff_qExpand_ofPowerSeries (N : ℕ) [NeZero N] (p : PowerSeries ℂ) (n : ℕ) :
    (ModularCurve.qExpand ℂ N (HahnSeries.ofPowerSeries ℤ ℂ p)).coeff (n : ℤ) =
      if N ∣ n then PowerSeries.coeff (n / N) p else 0 := by
  by_cases h : N ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [if_pos (Nat.dvd_mul_right N k), Nat.cast_mul, ModularCurve.qExpand_coeff_mul,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)), HahnSeries.ofPowerSeries_apply_coeff]
  · rw [if_neg h, ModularCurve.qExpand_coeff_of_not_dvd]
    exact fun h' => h (Int.natCast_dvd_natCast.mp h')

theorem coeff_qExpansion_N_delta (N : ℕ) [NeZero N] (n : ℕ) :
    PowerSeries.coeff n (qExpansion (N : ℝ) ModularForm.discriminant) =
      if N ∣ n then ((PowerSeries.coeff (n / N) dX : ℤ) : ℂ) else 0 := by
  have h := ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods DeltaMF
    one_mem_strictPeriods_SL N
  rw [coe_DeltaMF] at h
  have h2 := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) h
  simp only [HahnSeries.ofPowerSeries_apply_coeff] at h2
  rw [h2, coeff_qExpand_ofPowerSeries, qExpansion_one_delta]
  split_ifs <;> simp [PowerSeries.coeff_map]

theorem delta_slash_heckeDiag_eq_smul (d : ℕ) (hd : d ≠ 0) :
    (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d) =
      ((d : ℂ) ^ 11) • (fun τ : ℍ => ModularForm.discriminant (ModularForm.heckeDiagMatrix d • τ)) := by
  funext τ
  have h11 : ((d : ℂ) ^ ((12 : ℤ) - 1)) = (d : ℂ) ^ (11 : ℕ) := by
    rw [show ((12 : ℤ) - 1) = ((11 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [ModularForm.slash_heckeDiagMatrix_apply _ hd, Pi.smul_apply, smul_eq_mul, h11]

theorem coeff_qExpansion_one_delta_slash_heckeDiag (d : ℕ) (hd : d ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) =
      (d : ℂ) ^ 11 * (if d ∣ n then ((PowerSeries.coeff (n / d) dX : ℤ) : ℂ) else 0) := by

  have hT : AnalyticAt ℂ (cuspFunction 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) 0 := by
    have := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate DeltaMF (ModularForm.heckeDiagMatrix d))
      one_pos (one_mem_strictPeriods_conj d hd)
    simpa only [ModularForm.coe_translate, coe_DeltaMF] using this
  set g : ℍ → ℂ := fun τ : ℍ => ModularForm.discriminant (ModularForm.heckeDiagMatrix d • τ) with hg
  have hd11 : ((d : ℂ) ^ 11) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd)
  have hgT : g = ((d : ℂ) ^ 11)⁻¹ • (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d) := by
    rw [delta_slash_heckeDiag_eq_smul d hd, smul_smul, inv_mul_cancel₀ hd11, one_smul]
  have hqg : qExpansion 1 g = ((d : ℂ) ^ 11)⁻¹ • qExpansion 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d) := by
    rw [hgT]; exact UpperHalfPlane.qExpansion_smul hT _

  have hper : Function.Periodic (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) 1 := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
    simpa only [CuspForm.coe_discriminant, Complex.ofReal_one] using this
  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ModularForm.discriminant := by
    have := ModularFormClass.holo CuspForm.discriminant
    simpa only [CuspForm.coe_discriminant, Complex.ofReal_one] using this
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty ModularForm.discriminant := by
    have := ModularFormClass.bdd_at_infty CuspForm.discriminant
    simpa only [CuspForm.coe_discriminant, Complex.ofReal_one] using this
  have hc := UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hper hhol hbdd hd n
  simp only [ModularFormClass.qCoeff] at hc

  have : PowerSeries.coeff n (qExpansion 1 g) =
      ((d : ℂ) ^ 11)⁻¹ * PowerSeries.coeff n (qExpansion 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) := by
    rw [hqg, PowerSeries.coeff_smul, smul_eq_mul]
  have hc0 : PowerSeries.coeff n (qExpansion 1 g) =
      (if d ∣ n then PowerSeries.coeff (n / d) (qExpansion 1 ModularForm.discriminant) else 0) := hc
  rw [this] at hc0
  have hc' := congrArg (fun z => (d : ℂ) ^ 11 * z) hc0
  simp only [← mul_assoc, mul_inv_cancel₀ hd11, one_mul] at hc'
  rw [hc', qExpansion_one_delta]
  split_ifs <;> simp [PowerSeries.coeff_map]

theorem coeff_qExpansion_N_delta_slash_heckeDiag (d N : ℕ) (hd : d ≠ 0) [NeZero N] (n : ℕ) :
    PowerSeries.coeff n (qExpansion (N : ℝ) (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) =
      if N ∣ n then (d : ℂ) ^ 11 * (if d ∣ n / N then ((PowerSeries.coeff (n / N / d) dX : ℤ) : ℂ) else 0) else 0 := by
  have h := ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
    (ModularForm.translate DeltaMF (ModularForm.heckeDiagMatrix d)) (one_mem_strictPeriods_conj d hd) N
  rw [ModularForm.coe_translate, coe_DeltaMF] at h
  have h2 := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) h
  simp only [HahnSeries.ofPowerSeries_apply_coeff] at h2
  rw [h2, coeff_qExpand_ofPowerSeries]
  by_cases hN : N ∣ n
  · rw [if_pos hN, if_pos hN, coeff_qExpansion_one_delta_slash_heckeDiag d hd]
  · rw [if_neg hN, if_neg hN]

theorem intSeriesC_dX : ModularCurve.intSeriesC ℚ dX = ModularCurve.deltaSeries := by
  rw [ModularCurve.intSeriesC, ModularCurve.deltaSeries, ModularCurve.dedekindEtaUnitQ, dX, map_mul, PowerSeries.map_X,
    map_mul, HahnSeries.ofPowerSeries_X]

theorem deltaSeries_coeff_natCast (j : ℕ) :
    ModularCurve.deltaSeries.coeff (j : ℤ) = ((PowerSeries.coeff j dX : ℤ) : ℚ) := by
  rw [← intSeriesC_dX, ModularCurve.intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  rfl

theorem deltaSeries_coeff_neg {k : ℤ} (hk : k < 0) : ModularCurve.deltaSeries.coeff k = 0 :=
  ModularCurve.isMonicOfOrder_deltaSeries.coeff_of_lt (by omega)

theorem intSeriesC_mk_eq (N : ℕ) [NeZero N] (c : ℤ) :
    ModularCurve.intSeriesC ℚ (PowerSeries.mk fun n : ℕ => c * (if N ∣ n then PowerSeries.coeff (n / N) dX else 0)) =
      HahnSeries.C (c : ℚ) * ModularCurve.qExpand ℚ N ModularCurve.deltaSeries := by
  ext k
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, ModularCurve.intSeriesC]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    by_cases hN : N ∣ n
    · obtain ⟨j, rfl⟩ := hN
      rw [if_pos (Nat.dvd_mul_right N j), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)),
        Nat.cast_mul, ModularCurve.qExpand_coeff_mul, deltaSeries_coeff_natCast]
      simp
    · rw [if_neg hN, ModularCurve.qExpand_coeff_of_not_dvd _ _ (fun h' => hN (Int.natCast_dvd_natCast.mp h'))]
      simp
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · symm
      rw [mul_eq_zero]; right
      by_cases hN : (N : ℤ) ∣ k
      · obtain ⟨j, rfl⟩ := hN
        rw [ModularCurve.qExpand_coeff_mul]
        apply deltaSeries_coeff_neg
        have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        nlinarith
      · exact ModularCurve.qExpand_coeff_of_not_dvd _ _ hN
    · intro hmem
      obtain ⟨j, hj⟩ := hmem
      simp only [Nat.castOrderEmbedding_apply] at hj
      omega

theorem coeffMap_injective' {R S : Type*} [Field R] [Field S] (φ : R →+* S) :
    Function.Injective (ModularCurve.coeffMap φ) := by
  intro x y h
  ext n
  exact φ.injective (by simpa [ModularCurve.coeffMap_coeff] using congrArg (fun z => z.coeff n) h)

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : PowerSeries R) :
    ModularCurve.coeffMap φ (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map φ) := by
  ext n
  rw [ModularCurve.coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_intSeriesC {L : Type*} [Field L] [CharZero L]
    (ι : L →+* ℂ) (p : PowerSeries ℤ) {f : ℍ → ℂ} (hf : ModularCurve.IsIntegralQExp f p) :
    ModularCurve.coeffMap ι (ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ p)) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f) := by
  unfold ModularCurve.IsIntegralQExp at hf
  rw [ModularCurve.intSeriesC, ModularCurve.coeffEmb, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, ← hf]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem zpow_twelve_sub_one (c : ℂ) : c ^ ((12 : ℤ) - 1) = c ^ (11 : ℕ) := by
  rw [show ((12 : ℤ) - 1) = ((11 : ℕ) : ℤ) by norm_num, zpow_natCast]

theorem presentation (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M'] (hqM' : ¬ q ∣ M') (hℓM' : ¬ ℓ ∣ M')
    [NeZero (q * ℓ)] :
    ∃ (F G : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
        Subgroup (GL (Fin 2) ℝ)) 12) (pF pG : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp (⇑F) pF ∧ ModularCurve.IsIntegralQExp (⇑G) pG ∧
      ModularCurve.intSeriesC ℚ pF = HahnSeries.C ((((q * ℓ : ℕ) : ℤ) ^ 11 : ℤ) : ℚ) *
        ModularCurve.qExpand ℚ (q * ℓ) ModularCurve.deltaSeries ∧
      ModularCurve.intSeriesC ℚ pG = HahnSeries.C ((((q * ℓ : ℕ) : ℤ) ^ 11 * (q : ℤ) ^ 11 : ℤ) : ℚ) *
        ModularCurve.qExpand ℚ ((q * ℓ) * q) ModularCurve.deltaSeries ∧
      (∀ ρ : SL(2, ℤ), (⇑F) ∣[(12 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ = ⇑F) ∧
      (∀ ρ : SL(2, ℤ), (⇑G) ∣[(12 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ =
          ((ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix q) ∣[(12 : ℤ)] (ρ : GL (Fin 2) ℝ)) ∣[(12 : ℤ)]
            ModularForm.heckeDiagMatrix (q * ℓ)) ∧
      (⇑F = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix (q * ℓ)) ∧
      (⇑G = (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix q) ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix (q * ℓ)) := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hm0 : q * ℓ ≠ 0 := NeZero.ne _
  have hcop : Nat.Coprime (q * ℓ) M' :=
    Nat.Coprime.mul ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM')
  obtain ⟨F', hF'coe, hF'q, hF'sl⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix (q * ℓ) M' hcop 12 (DeltaG (q * ℓ))
  obtain ⟨G', hG'coe, hG'q, hG'sl⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix (q * ℓ) M' hcop 12
      (DeltaTG q (q * ℓ) hq0 (dvd_mul_right q ℓ))
  rw [coe_DeltaG] at hF'coe hF'q hF'sl
  rw [coe_DeltaTG] at hG'coe hG'q hG'sl
  refine ⟨F', G',
    PowerSeries.mk fun n : ℕ => (((q * ℓ : ℕ) : ℤ) ^ 11) * (if (q * ℓ) ∣ n then PowerSeries.coeff (n / (q * ℓ)) dX else 0),
    PowerSeries.mk fun n : ℕ => (((q * ℓ : ℕ) : ℤ) ^ 11 * (q : ℤ) ^ 11) *
      (if ((q * ℓ) * q) ∣ n then PowerSeries.coeff (n / ((q * ℓ) * q)) dX else 0),
    ?_, ?_, intSeriesC_mk_eq _ _, ?_, ?_, hG'sl, hF'coe, hG'coe⟩
  ·
    unfold ModularCurve.IsIntegralQExp
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hF'q n, zpow_twelve_sub_one, coeff_qExpansion_N_delta]
    split_ifs <;> simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_zero] <;> push_cast <;> ring
  ·
    unfold ModularCurve.IsIntegralQExp
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hG'q n, zpow_twelve_sub_one,
      coeff_qExpansion_N_delta_slash_heckeDiag q (q * ℓ) hq0]
    by_cases h1 : (q * ℓ) ∣ n
    · by_cases h2 : q ∣ n / (q * ℓ)
      · have h3 : (q * ℓ) * q ∣ n := (Nat.dvd_div_iff_mul_dvd h1).mp h2
        rw [if_pos h1, if_pos h2, if_pos h3, Nat.div_div_eq_div_mul]
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_zero]; push_cast; ring
      · have h3 : ¬ (q * ℓ) * q ∣ n := fun h => h2 ((Nat.dvd_div_iff_mul_dvd h1).mpr h)
        rw [if_pos h1, if_neg h2, if_neg h3]
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_zero]; push_cast; ring
    · have h3 : ¬ (q * ℓ) * q ∣ n := fun h => h1 (dvd_trans (dvd_mul_right _ _) h)
      rw [if_neg h1, if_neg h3]
      simp
  · haveI : NeZero ((q * ℓ) * q) := ⟨Nat.mul_ne_zero hm0 hq0⟩
    exact intSeriesC_mk_eq _ _
  · intro ρ
    rw [hF'sl ρ, coe_eq_mapGL, delta_slash_SL, hF'coe]

noncomputable def Dmq (m q : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℝ), 0; 0, (q : ℝ)]
    (by rw [Matrix.det_fin_two_of]; simp [hm, hq])

theorem val_Dmq (m q : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) :
    ((Dmq m q hm hq : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, (q : ℝ)] := rfl

theorem det_Dmq (m q : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) : ((Dmq m q hm hq).det : ℝ) = ((m * q : ℕ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_Dmq, Matrix.det_fin_two_of]; push_cast; ring

theorem det_Dmq_pos (m q : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) : 0 < ((Dmq m q hm hq).det : ℝ) := by
  rw [det_Dmq]; exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero hm hq)

theorem denom_Dmq (m q : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) (τ : ℍ) :
    UpperHalfPlane.denom (Dmq m q hm hq) τ = (q : ℂ) := by
  simp [UpperHalfPlane.denom, val_Dmq]

theorem Dmq_smul (q ℓ : ℕ) (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hm : q * ℓ ≠ 0) (τ : ℍ) :
    Dmq (q * ℓ) q hm hq • τ = ModularForm.heckeDiagMatrix ℓ • τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_Dmq_pos _ _ hm hq), ModularForm.coe_heckeDiagMatrix_smul hℓ]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_Dmq]
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  simp
  field_simp

def weylLift (q : ℕ) (ρ : SL(2, ℤ)) (h : (q : ℤ) ∣ (ρ 1 1 : ℤ)) (hq : q ≠ 0) : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * (ρ 0 0 : ℤ), (ρ 0 1 : ℤ); (ρ 1 0 : ℤ), (ρ 1 1 : ℤ) / (q : ℤ)], by
    have hdet := Matrix.SpecialLinearGroup.det_coe ρ
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    obtain ⟨c, hc⟩ := h
    rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hq)]
    rw [hc] at hdet
    linear_combination hdet⟩

theorem weyl_identity (q ℓ : ℕ) (hq : q ≠ 0) (hm : q * ℓ ≠ 0) (ρ : SL(2, ℤ)) (h : (q : ℤ) ∣ (ρ 1 1 : ℤ)) :
    ModularForm.heckeDiagMatrix q * Matrix.SpecialLinearGroup.mapGL ℝ ρ * ModularForm.heckeDiagMatrix (q * ℓ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (weylLift q ρ h hq) * Dmq (q * ℓ) q hm hq := by
  obtain ⟨c, hc⟩ := h
  have hcd : ((ρ 1 1 : ℤ) / (q : ℤ) : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hq)]
  have e00 : ((weylLift q ρ ⟨c, hc⟩ hq : SL(2, ℤ)) 0 0 : ℤ) = q * ρ 0 0 := rfl
  have e01 : ((weylLift q ρ ⟨c, hc⟩ hq : SL(2, ℤ)) 0 1 : ℤ) = ρ 0 1 := rfl
  have e10 : ((weylLift q ρ ⟨c, hc⟩ hq : SL(2, ℤ)) 1 0 : ℤ) = ρ 1 0 := rfl
  have e11 : ((weylLift q ρ ⟨c, hc⟩ hq : SL(2, ℤ)) 1 1 : ℤ) = c := hcd
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_apply, ModularForm.val_heckeDiagMatrix hq, ModularForm.val_heckeDiagMatrix hm,
    mapGL_apply, val_Dmq]
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, hc] <;> push_cast <;> ring

theorem delta_slash_Dmq (q ℓ : ℕ) (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hm : q * ℓ ≠ 0) :
    ModularForm.discriminant ∣[(12 : ℤ)] Dmq (q * ℓ) q hm hq =
      ((q : ℂ) ^ 10) • (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix ℓ) := by
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, ModularForm.slash_heckeDiagMatrix_apply _ hℓ, ModularForm.slash_apply,
    UpperHalfPlane.σ, if_pos (det_Dmq_pos _ _ hm hq), det_Dmq, denom_Dmq, Dmq_smul q ℓ hq hℓ hm]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [zpow_twelve_sub_one, zpow_twelve_sub_one, zpow_neg, zpow_ofNat]
  push_cast
  field_simp

theorem analyticAt_delta_slash_heckeDiag (d : ℕ) (hd : d ≠ 0) :
    AnalyticAt ℂ (cuspFunction 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) 0 := by
  have := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate DeltaMF (ModularForm.heckeDiagMatrix d))
    one_pos (one_mem_strictPeriods_conj d hd)
  simpa only [ModularForm.coe_translate, coe_DeltaMF] using this

noncomputable def DeltaC : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map (Int.castRingHom ℂ) dX)

theorem ofPowerSeries_qExpansion_delta_slash_heckeDiag (d : ℕ) (hd : d ≠ 0) [NeZero d] :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix d)) =
      HahnSeries.C ((d : ℂ) ^ 11) * ModularCurve.qExpand ℂ d DeltaC := by
  ext k
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_qExpansion_one_delta_slash_heckeDiag d hd, DeltaC,
      coeff_qExpand_ofPowerSeries]
    split_ifs <;> simp [PowerSeries.coeff_map]
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · symm; rw [mul_eq_zero]; right
      by_cases hN : (d : ℤ) ∣ k
      · obtain ⟨j, rfl⟩ := hN
        rw [ModularCurve.qExpand_coeff_mul, DeltaC, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
        intro hmem; obtain ⟨i, hi⟩ := hmem
        simp only [Nat.castOrderEmbedding_apply] at hi
        have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
        nlinarith
      · exact ModularCurve.qExpand_coeff_of_not_dvd _ _ hN
    · intro hmem; obtain ⟨j, hj⟩ := hmem
      simp only [Nat.castOrderEmbedding_apply] at hj
      omega

theorem coeffMap_coeffEmb_deltaSeries {L : Type*} [Field L] [CharZero L] (ι : L →+* ℂ) :
    ModularCurve.coeffMap ι (ModularCurve.coeffEmb L ModularCurve.deltaSeries) = DeltaC := by
  rw [← intSeriesC_dX, ModularCurve.intSeriesC, ModularCurve.coeffEmb, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, DeltaC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_C {L : Type*} [Field L] [CharZero L] (ι : L →+* ℂ) (r : ℚ) :
    ModularCurve.coeffMap ι (ModularCurve.coeffEmb L (HahnSeries.C r)) = HahnSeries.C ((r : ℂ)) := by
  rw [ModularCurve.coeffEmb, HahnSeries.C_apply, ModularCurve.coeffMap_single, ModularCurve.coeffMap_single, ← HahnSeries.C_apply,
    eq_ratCast, map_ratCast]

theorem coeffMap_coeffEmb_qExpand {L : Type*} [Field L] [CharZero L] (ι : L →+* ℂ) (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    ModularCurve.coeffMap ι (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ N x)) =
      ModularCurve.qExpand ℂ N (ModularCurve.coeffMap ι (ModularCurve.coeffEmb L x)) := by
  rw [ModularCurve.coeffEmb, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]

end OggPres
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries.OggPres"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (x : ↥K) (hx : ((x : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K τ)
    (hdvd : (q : ℤ) ∣ (δ 0 0 : ℤ))
    (w : ↥K) (hw : ((w : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q))) :
    τ x * w = algebraMap L ↥K ((q : L) ^ 12) := by
  classical
  obtain ⟨ι, hι⟩ := hι
  haveI hmz : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  obtain ⟨F, G, pF, pG, hF, hG, hpF, hpG, hFsl, hGsl, hFcoe, hGcoe⟩ := OggPres.presentation q ℓ M' hqM' hℓM'

  have hΔ0 : ModularCurve.deltaSeries ≠ 0 := ModularCurve.deltaSeries_ne_zero
  have ha : ((((q * ℓ : ℕ) : ℤ) ^ 11 : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]; exact pow_ne_zero _ (by exact_mod_cast hmz.ne)
  have hb : (((q : ℤ) ^ 11 : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]; exact pow_ne_zero _ (by exact_mod_cast hq0)
  haveI : NeZero ((q * ℓ) * q) := ⟨Nat.mul_ne_zero hmz.ne hq0⟩
  have hEmq : ModularCurve.qExpand ℚ ((q * ℓ) * q) ModularCurve.deltaSeries ≠ 0 :=
    (map_ne_zero_iff _ (ModularCurve.qExpand_injective _)).mpr hΔ0
  have hpG0 : ModularCurve.intSeriesC ℚ pG ≠ 0 := by
    rw [hpG, Int.cast_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero (HahnSeries.C_ne_zero ha) (HahnSeries.C_ne_zero hb)) hEmq

  have hratio : ModularCurve.intSeriesC ℚ pF / ModularCurve.intSeriesC ℚ pG =
      (HahnSeries.C ((((q : ℤ) ^ 11 : ℤ) : ℚ)))⁻¹ * ModularCurve.qExpand ℚ (q * ℓ) (ModularCurve.modularUnitSeries q) := by
    rw [hpF, hpG, ModularCurve.modularUnitSeries, ModularCurve.deltaSeriesN, map_mul (ModularCurve.qExpand ℚ (q * ℓ)),
      map_inv₀ (ModularCurve.qExpand ℚ (q * ℓ)), ModularCurve.qExpand_qExpand, Int.cast_mul, map_mul HahnSeries.C]
    have hCa : (HahnSeries.C ((((q * ℓ : ℕ) : ℤ) ^ 11 : ℤ) : ℚ) : LaurentSeries ℚ) ≠ 0 := HahnSeries.C_ne_zero ha
    have hCb : (HahnSeries.C (((q : ℤ) ^ 11 : ℤ) : ℚ) : LaurentSeries ℚ) ≠ 0 := HahnSeries.C_ne_zero hb
    field_simp

  set cq : L := (algebraMap ℚ L ((((q : ℤ) ^ 11 : ℤ) : ℚ)))⁻¹ with hcq
  have hcq0 : cq ≠ 0 := by
    rw [hcq]; apply inv_ne_zero
    rw [map_ne_zero_iff _ (algebraMap ℚ L).injective]; exact hb
  set X : ↥K := algebraMap L ↥K cq * x with hXdef
  have hX : ((X : ↥K) : LaurentSeries L) =
      ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pF / ModularCurve.intSeriesC ℚ pG) := by
    rw [hratio, map_mul, hXdef]
    have e1 : (((algebraMap L ↥K cq * x : ↥K)) : LaurentSeries L) = algebraMap L (LaurentSeries L) cq * ((x : ↥K) : LaurentSeries L) := rfl
    rw [e1, hx, ModularCurve.coeffEmb, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    congr 1
    rw [map_inv₀ (ModularCurve.coeffMap (algebraMap ℚ L)), HahnSeries.C_apply, ModularCurve.coeffMap_single,
      ModularCurve.algebraMap_laurentSeries_eq_single, hcq, ← HahnSeries.C_apply, ← HahnSeries.C_apply, map_inv₀]

  have hτ' := hτ
  dsimp only [ModularCurve.FullLevel.IsLevelAutAt] at hτ'
  have hι' : ι ξ = Complex.exp (2 * Real.pi * Complex.I / ((q * ℓ : ℕ) : ℂ)) := by
    first
      | exact hι
      | (rw [Nat.cast_mul]; exact hι)
      | (simpa using hι)
  have E1 := hτ' 12 F G pF pG hF hG hpG0 X hX ι hι'
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  haveI : NeZero ℓ := ⟨hℓ0⟩

  have hdvd' : (q : ℤ) ∣ ((δ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hdvd
  rw [hFsl, hGsl, OggPres.coe_eq_mapGL, ← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc,
    OggPres.weyl_identity q ℓ hq0 hmz.ne (δ⁻¹) hdvd', SlashAction.slash_mul, OggPres.delta_slash_SL,
    OggPres.delta_slash_Dmq q ℓ hq0 hℓ0 hmz.ne,
    UpperHalfPlane.qExpansion_smul (OggPres.analyticAt_delta_slash_heckeDiag ℓ hℓ0),
    PowerSeries.smul_eq_C_mul, map_mul (HahnSeries.ofPowerSeries ℤ ℂ), HahnSeries.ofPowerSeries_C,
    OggPres.ofPowerSeries_qExpansion_delta_slash_heckeDiag ℓ hℓ0] at E1

  set T : LaurentSeries ℂ := ModularCurve.coeffMap ι ((τ x : ↥K) : LaurentSeries L) with hT
  set W : LaurentSeries ℂ := ModularCurve.coeffMap ι ((w : ↥K) : LaurentSeries L) with hW
  set Eℓ : LaurentSeries ℂ := ModularCurve.qExpand ℂ ℓ OggPres.DeltaC with hEℓ
  set Em : LaurentSeries ℂ := ModularCurve.qExpand ℂ (q * ℓ) OggPres.DeltaC with hEm
  have hΔC0 : OggPres.DeltaC ≠ 0 := by
    rw [← OggPres.coeffMap_coeffEmb_deltaSeries ι]
    exact (map_ne_zero_iff _ (OggPres.coeffMap_injective' ι)).mpr
      ((map_ne_zero_iff _ (OggPres.coeffMap_injective' _)).mpr hΔ0)
  have hEm0 : Em ≠ 0 := (map_ne_zero_iff _ (ModularCurve.qExpand_injective _)).mpr hΔC0
  have hEℓ0 : Eℓ ≠ 0 := (map_ne_zero_iff _ (ModularCurve.qExpand_injective _)).mpr hΔC0

  have hFser : HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F) = HahnSeries.C (((q * ℓ : ℕ) : ℂ) ^ 11) * Em := by
    rw [← OggPres.coeffMap_coeffEmb_intSeriesC ι pF hF, hpF, map_mul, map_mul, OggPres.coeffMap_coeffEmb_C,
      OggPres.coeffMap_coeffEmb_qExpand, OggPres.coeffMap_coeffEmb_deltaSeries]
    congr 2
    push_cast; ring

  have hTX : ModularCurve.coeffMap ι ((τ X : ↥K) : LaurentSeries L) = HahnSeries.C (ι cq) * T := by
    rw [hXdef, map_mul, AlgEquiv.commutes]
    have e2 : (((algebraMap L ↥K cq * τ x : ↥K)) : LaurentSeries L) = algebraMap L (LaurentSeries L) cq * ((τ x : ↥K) : LaurentSeries L) := rfl
    rw [e2, map_mul, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single, ← HahnSeries.C_apply]

  have hWE : W = Eℓ * Em⁻¹ := by
    rw [hW, hw, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, ModularCurve.modularUnitSeries, ModularCurve.deltaSeriesN,
      map_mul (ModularCurve.coeffEmb L), map_inv₀ (ModularCurve.coeffEmb L), map_mul (ModularCurve.coeffMap ι),
      map_inv₀ (ModularCurve.coeffMap ι), OggPres.coeffMap_coeffEmb_qExpand, OggPres.coeffMap_coeffEmb_deltaSeries,
      map_mul (ModularCurve.qExpand ℂ ℓ), map_inv₀ (ModularCurve.qExpand ℂ ℓ), ModularCurve.qExpand_qExpand,
      ModularCurve.qExpand_congr (mul_comm ℓ q)]

  rw [hTX, hFser] at E1
  have hιcq : ι cq = ((q : ℂ) ^ 11)⁻¹ := by
    rw [hcq, map_inv₀, eq_ratCast, map_ratCast]; push_cast; ring
  set kk : ℂ := ι cq * ((q : ℂ) ^ 10 * (ℓ : ℂ) ^ 11) with hkk
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  have hkk0 : kk ≠ 0 := by
    rw [hkk, hιcq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) (mul_ne_zero (pow_ne_zero _ hqC) (pow_ne_zero _ hℓC))
  have h2 : HahnSeries.C kk * (T * Eℓ) = HahnSeries.C (((q * ℓ : ℕ) : ℂ) ^ 11) * Em := by
    rw [← E1, hkk, map_mul, map_mul]; ring
  have hnum : kk * (q : ℂ) ^ 12 = ((q * ℓ : ℕ) : ℂ) ^ 11 := by
    rw [hkk, hιcq]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    push_cast; field_simp
  have hTW : T * W = HahnSeries.C ((q : ℂ) ^ 12) := by
    rw [hWE]
    apply mul_left_cancel₀ (HahnSeries.C_ne_zero hkk0)
    apply mul_right_cancel₀ hEm0
    calc HahnSeries.C kk * (T * (Eℓ * Em⁻¹)) * Em = HahnSeries.C kk * (T * Eℓ) * (Em⁻¹ * Em) := by ring
      _ = HahnSeries.C (((q * ℓ : ℕ) : ℂ) ^ 11) * Em := by rw [h2, inv_mul_cancel₀ hEm0, mul_one]
      _ = HahnSeries.C kk * HahnSeries.C ((q : ℂ) ^ 12) * Em := by rw [← map_mul, hnum]

  apply Subtype.ext
  apply OggPres.coeffMap_injective' ι
  have e3 : (((τ x * w : ↥K)) : LaurentSeries L) = ((τ x : ↥K) : LaurentSeries L) * ((w : ↥K) : LaurentSeries L) := rfl
  have e4 : (((algebraMap L ↥K ((q : L) ^ 12) : ↥K)) : LaurentSeries L) = algebraMap L (LaurentSeries L) ((q : L) ^ 12) := rfl
  rw [e3, e4, map_mul, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single, ← HahnSeries.C_apply,
    map_pow, map_natCast]
  exact hTW

end S_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries (solution)
