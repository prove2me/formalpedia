-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_diffQExpBar_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cf7728b2-a52e-50d1-81a9-c190e8e6be66

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import Theorems.Thm_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane HahnSeries
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qEuler qEuler_coeff diffQExp_smul_D diffQExpBar modularFunctionFieldBar qExpand_one_apply jq coeff_jq_neg_one jqd_mem_full coeffMap coeffMap_coeff coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div jqModC_eq_qExpansion_E4_cube_div_discriminant"
namespace DiffQExpDescent
p2m_open "ModularCurve"

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

def thetaPS (p : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p

theorem thetaPS_eq (p : PowerSeries R) :
    thetaPS p = PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p := rfl

theorem qEuler_ofPowerSeries (p : PowerSeries R) :
    qEuler R (ofPowerSeries ℤ R p) = ofPowerSeries ℤ R (thetaPS p) := by
  ext m
  rw [qEuler_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hm
  · rw [mul_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hm)
    simp [thetaPS, PowerSeries.coeff_mk]

theorem coeffMap_qEuler (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f (qEuler R x) = qEuler S (coeffMap f x) := by
  ext m
  simp

theorem coeffMap_ofPowerSeries_eq (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext m
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_C (f : R →+* S) (c : R) : coeffMap f (C c) = C (f c) :=
  HahnSeries.map_C c f

end Laurent

section Level

variable {N : ℕ}

abbrev qL (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) :
    qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (ModularForm.mcast h f) = qL f := by
  simp only [qL, ModularForm.coe_mcast]

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa [qL] using h

theorem ne_zero_of_qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : qL f ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply h
  simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]

end Level

section LevelOne

def E4cube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_E4cube : (E4cube : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄ * ModularForm.E₄ := by
  simp only [E4cube, ModularForm.coe_mcast, ModularForm.coe_mul]

theorem qL_E4cube : qL E4cube = qL ModularForm.E₄ ^ 3 := by
  rw [coe_E4cube, qL, ← ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, PowerSeries.coe_mul, PowerSeries.coe_mul]
  ring

def DeltaMF : ModularForm 𝒮ℒ 12 := ModularFormClass.modularForm CuspForm.discriminant

theorem coe_DeltaMF : (DeltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem DeltaMF_apply_ne_zero (z : ℍ) : DeltaMF z ≠ 0 := by
  rw [coe_DeltaMF]
  exact ModularForm.discriminant_ne_zero z

end LevelOne

section Main

variable (N : ℕ) [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ)

local notation "ℚb" => AlgebraicClosure ℚ

def jBar : LaurentSeries ℚb := coeffEmb ℚb jq

theorem jBar_mem : jBar ∈ modularFunctionFieldBar N := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  refine coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ?_
  simpa [qExpand_one_apply] using jqd_mem_full (N := N) (d := 1) (one_dvd N)

theorem coeffMap_jBar : coeffMap ι₀ jBar = jqModC ℂ := by
  rw [jBar, coeffEmb, coeffMap_coeffMap, ← jqModC_rat]
  exact map_jqModC _

theorem qEuler_jBar_ne_zero : qEuler ℚb jBar ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries ℚb => x.coeff (-1)) h
  simp only [qEuler_coeff, jBar, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_one,
    HahnSeries.coeff_zero, Int.cast_neg, Int.cast_one, neg_eq_zero, one_ne_zero] at h1

variable (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
  (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ ι₀.range)

def fBarPS : PowerSeries ℚb := PowerSeries.mk fun n : ℕ => Classical.choose (hf n)

theorem map_fBarPS : (fBarPS N ι₀ f hf).map ι₀ = qExpansion 1 f := by
  ext n
  rw [PowerSeries.coeff_map, fBarPS, PowerSeries.coeff_mk]
  exact Classical.choose_spec (hf n)

def fBar : LaurentSeries ℚb := ofPowerSeries ℤ ℚb (fBarPS N ι₀ f hf)

theorem coeffMap_fBar : coeffMap ι₀ (fBar N ι₀ f hf) = qL f := by
  rw [fBar, coeffMap_ofPowerSeries_eq, map_fBarPS]

def xBar : LaurentSeries ℚb := fBar N ι₀ f hf / qEuler ℚb jBar

theorem xBar_mul_qEuler_jBar : xBar N ι₀ f hf * qEuler ℚb jBar = fBar N ι₀ f hf :=
  div_mul_cancel₀ _ qEuler_jBar_ne_zero

theorem xBar_mem : xBar N ι₀ f hf ∈ modularFunctionFieldBar N := by

  obtain ⟨G, hG⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne N E4cube
  obtain ⟨Dl, hDl⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne N DeltaMF

  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq
    (Γ := CongruenceSubgroup.Gamma0 N) (one_mem_strictPeriods N) Dl G

  set a : LaurentSeries ℂ := qL G with ha
  set b : LaurentSeries ℂ := qL Dl with hb
  set Da : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 G)) with hDa
  set Db : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 Dl)) with hDb
  set W : LaurentSeries ℂ := b * Da - Db * a with hW

  have hDl0 : Dl ≠ 0 := by
    intro h0
    have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 12 => (F : ℍ → ℂ) I) h0
    simp only [hDl, ModularForm.coe_zero, Pi.zero_apply] at this
    exact DeltaMF_apply_ne_zero I this
  have hb0 : b ≠ 0 := qL_ne_zero Dl hDl0

  have hBq : qL B = C (12 : ℂ) * W := by
    rw [qL, hB]
    simp only [map_sub, map_mul, ofPowerSeries_C, ← thetaPS_eq]
    push_cast
    ring

  have hj : coeffMap ι₀ jBar = a / b := by
    rw [coeffMap_jBar, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ha, hb, hG, hDl,
      qL_E4cube, coe_DeltaMF]
  have hT : coeffMap ι₀ (qEuler ℚb jBar) = b⁻¹ ^ 2 * W := by
    rw [coeffMap_qEuler, hj, Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      ha, hb, qL, qL, qEuler_ofPowerSeries, qEuler_ofPowerSeries, ← hDa, ← hDb, hW]
    ring
  have hT0 : coeffMap ι₀ (qEuler ℚb jBar) ≠ 0 :=
    (map_ne_zero (coeffMap ι₀)).mpr qEuler_jBar_ne_zero
  have hW0 : W ≠ 0 := by
    intro hW0
    apply hT0
    rw [hT, hW0, mul_zero]
  have hB0 : B ≠ 0 := by
    refine ne_zero_of_qL_ne_zero B ?_
    rw [hBq]
    exact mul_ne_zero (C_ne_zero (by norm_num)) hW0

  let Fm : ModularForm (CongruenceSubgroup.Gamma0 N) 2 := ModularFormClass.modularForm f
  let Gnum : ModularForm (CongruenceSubgroup.Gamma0 N) (12 + 12 + 2) :=
    ModularForm.mcast (by norm_num) ((Fm.mul Dl).mul Dl)
  have hGnum : qL Gnum = qL f * b * b := by
    simp only [Gnum, qL_mcast, qL_mul, hb]
    rfl

  have h12 : (12 : ℚb) ≠ 0 := by norm_num
  set x' : LaurentSeries ℚb := C (12 : ℚb)⁻¹ * xBar N ι₀ f hf with hx'
  have hx'C : coeffMap ι₀ x' = qL Gnum / qL B := by
    have hc : (C (12 : ℂ) : LaurentSeries ℂ) ≠ 0 := C_ne_zero (by norm_num)
    rw [hx', map_mul, coeffMap_C, map_inv₀, map_ofNat, map_inv₀, xBar, map_div₀, coeffMap_fBar, hT,
      hGnum, hBq]
    field_simp
  have hx'mem : x' ∈ modularFunctionFieldBar N :=
    ModularCurve.mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div N Gnum B hB0 ι₀ x' hx'C

  have hxx : xBar N ι₀ f hf = C (12 : ℚb) * x' := by
    rw [hx', ← mul_assoc, ← map_mul, mul_inv_cancel₀ h12, map_one, one_mul]
  rw [hxx]
  refine mul_mem ?_ hx'mem
  have h12mem := (modularFunctionFieldBar N).algebraMap_mem (12 : ℚb)
  rwa [algebraMap_laurentSeries_eq_single, ← C_apply] at h12mem

def omega : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  (⟨xBar N ι₀ f hf, xBar_mem N ι₀ f hf⟩ : modularFunctionFieldBar N) •
    KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (⟨jBar, jBar_mem N⟩ : modularFunctionFieldBar N)

theorem diffQExpBar_omega : diffQExpBar N (omega N ι₀ f hf) = fBar N ι₀ f hf := by
  rw [omega, diffQExpBar, diffQExp_smul_D]
  exact xBar_mul_qEuler_jBar N ι₀ f hf

theorem coeffMap_diffQExpBar_omega :
    coeffMap ι₀ (diffQExpBar N (omega N ι₀ f hf)) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f) := by
  rw [diffQExpBar_omega, coeffMap_fBar]

end Main

end ModularCurve.DiffQExpDescent

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion.ModularCurve in
theorem solution (N : ℕ) [NeZero N]
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ ι₀.range) :
    ∃ ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExpBar N ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) :=
  ⟨ModularCurve.DiffQExpDescent.omega N ι₀ f hf,
    ModularCurve.DiffQExpDescent.coeffMap_diffQExpBar_omega N ι₀ f hf⟩

end S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion (solution)
