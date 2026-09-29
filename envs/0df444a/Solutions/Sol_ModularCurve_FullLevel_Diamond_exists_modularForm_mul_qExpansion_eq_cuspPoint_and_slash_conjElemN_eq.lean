-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/c6c76125-eab9-581b-9e4f-54212e83a0bf

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma
import Theorems.Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
import Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
import Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase
import Theorems.Thm_ModularCurve_equation_tateBase_tateToricPoint
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_equation_tateBase_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLA
variable (m : ℕ) [NeZero m]

theorem mpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [mne m])

@[scoped simp] theorem Dr_coe : ((Dr m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] := rfl

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr m * conjElemN m γ = (γ : GL (Fin 2) ℝ) * Dr m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (mne m), mul_comm]

theorem conjElemN_eq (γ : SL(2, ℤ)) : conjElemN m γ = (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem conjElemN_mul (γ δ : SL(2, ℤ)) : conjElemN m (γ * δ) = conjElemN m γ * conjElemN m δ := by
  simp only [conjElemN_eq, map_mul]; group

theorem conjElemN_one : conjElemN m 1 = 1 := by
  simp only [conjElemN_eq, map_one]; group

theorem conjElemN_inv (γ : SL(2, ℤ)) : conjElemN m γ⁻¹ = (conjElemN m γ)⁻¹ := by
  simp only [conjElemN_eq, map_inv]; group

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

private theorem _root_.W1xLA.det_conjElemN_val (γ : SL(2, ℤ)) : ((conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

p2m_export "W1xLA" "det_conjElemN_val"

variable {m}

def upMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, (m : ℤ) * δ 0 1; δ 1 0 / m, δ 1 1]

theorem det_upMat (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : (upMat (m := m) δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def upSL (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨upMat (m := m) δ, det_upMat δ h⟩

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / m; (m : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : (downMat (m := m) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (m := m) ε, det_downMat ε h⟩

theorem upSL_coe (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) :
    ((upSL δ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr m = Dr m * (δ : GL (Fin 2) ℝ) := by
  obtain ⟨c, hc⟩ := h
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upSL, upMat, hc, h1] <;> ring

theorem downSL_coe (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    Dr m * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr m := by
  obtain ⟨b, hb⟩ := h
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

namespace W1xLA
variable (m : ℕ) [NeZero m] (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')

private abbrev _root_.W1xLA.Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

p2m_export "W1xLA" "Γ"
variable {m M'}

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

abbrev SLq (m : ℕ) : SL(2, ℤ) →* SL(2, ZMod m) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m))

theorem SLq_apply (A : SL(2, ℤ)) (i j : Fin 2) : (SLq m A) i j = ((A i j : ℤ) : ZMod m) := by
  simp

omit [NeZero m] in
theorem q_dvd_level : (m : ℤ) ∣ ((m ^ 2 * M' : ℕ) : ℤ) := ⟨m * M', by push_cast; ring⟩

theorem SLq_eq_one_iff (A : SL(2, ℤ)) : SLq m A = 1 ↔
    ((A 0 0 : ℤ) : ZMod m) = 1 ∧ ((A 0 1 : ℤ) : ZMod m) = 0 ∧ ((A 1 0 : ℤ) : ZMod m) = 0 ∧
      ((A 1 1 : ℤ) : ZMod m) = 1 := by
  constructor
  · intro h
    have e : ∀ i j, ((A i j : ℤ) : ZMod m) = (1 : SL(2, ZMod m)) i j := fun i j => by
      rw [← SLq_apply, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e]
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    rw [SLq_apply]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    SLq m (upSL δ (q_dvd_lowerLeft_of_mem_GH hδ)) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod m) = 1
    exact upperLeft_of_mem_GH hδ
  · show (((m : ℤ) * δ 0 1 : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / m : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  · show ((δ 1 1 : ℤ) : ZMod m) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / m : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨m * c, ?_⟩
  push_cast
  rw [show (m : ℤ) ^ 2 * M' * c = m * (M' * (m * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    ∃ δ' ∈ GH m M', ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m γ * (δ : GL (Fin 2) ℝ) * (conjElemN m γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq m ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hδ, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨e00, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hεq
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hδ)) (inv_mem hγ)
  have h01 : (m : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨downSL ε h01, ?_, ?_⟩
  · rw [mem_GH_iff]
    refine ⟨?_, e11⟩
    show (((m : ℤ) * ε 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hq : (m : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
    have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
    have hcop : IsCoprime (m : ℤ) (M' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hmM'
    obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
    refine ⟨c, ?_⟩
    rw [hc]; push_cast; ring
  · obtain ⟨c, hc⟩ := h01

    have hd := downSL_coe ε ⟨c, hc⟩
    have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hδ)
    rw [← hu] at hup
    have e1 : ((downSL ε ⟨c, hc⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr m)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr m := by
      rw [mul_assoc, ← hd, inv_mul_cancel_left]
    have e2 : (u : GL (Fin 2) ℝ) = Dr m * (δ : GL (Fin 2) ℝ) * (Dr m)⁻¹ := by
      rw [← hup, mul_inv_cancel_right]
    rw [e1, hε]
    simp only [map_mul, map_inv]
    rw [e2, conjElemN_eq]
    group

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ m M' ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hmM' hγ hδ
  exact ⟨δ', hδ', e⟩

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ}

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

section Slash

variable (hmM' : Nat.Coprime m M')
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ModularForm (Γ m M') k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

omit hmM' in
private theorem _root_.W1xLA.σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

p2m_export "W1xLA" "σ_conjElemN_apply"
@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_mul_apply {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ m M') k₁) (g : ModularForm (Γ m M') k₂) :
    ⇑(sl hmM' γ hγ (f.mul g)) = ⇑(sl hmM' γ hγ f) * ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElemN_val, abs_one, one_smul]

theorem sl_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ m M') k) :
    sl hmM' γ hγ (f + g) = sl hmM' γ hγ f + sl hmM' γ hγ g := by
  ext τ
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, ModularForm.add_apply]

theorem sl_smul {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ (c • f)) = c • ⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_conjElemN_apply]

theorem sl_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ (-f)) = -⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

theorem sl_sl {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M')
    (f : ModularForm (Γ m M') k) :
    sl hmM' δ hδ (sl hmM' γ hγ f) = sl hmM' (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_sl, conjElemN_mul, SlashAction.slash_mul]

theorem sl_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (f : ModularForm (Γ m M') k) : sl hmM' γ hγ f = sl hmM' γ' hγ' f := by
  subst h; rfl

theorem sl_one {k : ℤ} (f : ModularForm (Γ m M') k) : sl hmM' 1 (one_mem _) f = f := by
  ext τ
  simp only [coe_sl, conjElemN_one, SlashAction.slash_one]

theorem sl_inv_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    sl hmM' γ⁻¹ (inv_mem hγ) (sl hmM' γ hγ f) = f := by
  rw [sl_sl, sl_congr hmM' (mul_inv_cancel γ) _ (one_mem _), sl_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M') k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_inv_sl hmM' γ hγ f, h]
  ext τ
  simp [coe_sl]

theorem sl_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : sl hmM' γ hγ (0 : ModularForm (Γ m M') k) = 0 := by
  ext τ; simp [coe_sl]

theorem sl_const (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    sl hmM' γ hγ (ModularForm.const c : ModularForm (Γ m M') 0) = ModularForm.const c := by
  ext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElemN_apply,
    det_conjElemN_val, ModularForm.const_apply]
  simp

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section QExp

private def _root_.W1xLA.qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

p2m_export "W1xLA" "qC"
private theorem _root_.W1xLA.qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M') k₁) (g : ModularForm (Γ m M') k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

p2m_export "W1xLA" "qC_mul"
theorem qC_add {k : ℤ} (f g : ModularForm (Γ m M') k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ m M') k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ m M') k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ m M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit [NeZero m] in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ m M') 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ m M') 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ m M') 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

theorem qC_sum_smul {k : ℤ} (s : Finset ℕ) (c : ℕ → ℂ) (h : ℕ → ModularForm (Γ m M') k) :
    qC (∑ j ∈ s, c j • (⇑(h j) : ℍ → ℂ)) = ∑ j ∈ s, HahnSeries.C (c j) * qC (h j) := by
  classical
  have hcoe : ∀ t : Finset ℕ, (∑ j ∈ t, c j • (⇑(h j) : ℍ → ℂ)) = ⇑(∑ j ∈ t, c j • h j) := fun t => by
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]
  induction s using Finset.induction_on with
  | empty => simp [qC_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hcoe t, ← ModularForm.IsGLPos.coe_smul, qC_add,
        ModularForm.IsGLPos.coe_smul, qC_smul, ← hcoe t, ih]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M') k₁) (f₂ : ModularForm (Γ m M') k₂)
    (f₃ : ModularForm (Γ m M') k₃) (f₄ : ModularForm (Γ m M') k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ m M') (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem slash_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M') k₁) (f₂ : ModularForm (Γ m M') k₂)
    (f₃ : ModularForm (Γ m M') k₃) (f₄ : ModularForm (Γ m M') k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    (⇑(sl hmM' γ hγ f₁) * ⇑(sl hmM' γ hγ f₂) : ℍ → ℂ) = ⇑(sl hmM' γ hγ f₃) * ⇑(sl hmM' γ hγ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] conjElemN m γ) h
  rw [ModularForm.mul_slash] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash]
  simpa only [coe_sl, det_conjElemN_val, abs_one, one_smul] using h'

theorem qC_sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {g : ModularForm (Γ m M') k}
    (hg : g ≠ 0) : qC (sl hmM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hmM' γ hγ hg ((qC_eq_zero_iff _).mp h)

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Img

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def IsImgC (w w' : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γ m M') k), g ≠ 0 ∧ w = qC f / qC g ∧
    w' * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f)

variable {hmM' γ hγ}

theorem IsImgC.apply_rep {w w' : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ w w') {k : ℤ}
    (f g : ModularForm (Γ m M') k) (hg : g ≠ 0) (hw : w = qC f / qC g) :
    w' * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f) := by
  obtain ⟨k₂, f₂, g₂, hg₂, hw₂, hy⟩ := h
  have hg' : qC g ≠ 0 := fun e => hg ((qC_eq_zero_iff g).mp e)
  have hg₂' : qC g₂ ≠ 0 := fun e => hg₂ ((qC_eq_zero_iff g₂).mp e)
  have hq : qC f * qC g₂ = qC f₂ * qC g := by
    rw [← div_eq_div_iff hg' hg₂', ← hw, ← hw₂]
  have hfun := mul_eq_mul_of_qC f g₂ f₂ g (add_comm k₂ k) hq
  have hsl := slash_mul_eq hmM' f g₂ f₂ g (add_comm k₂ k) hfun γ hγ
  have hqs : qC (sl hmM' γ hγ f) * qC (sl hmM' γ hγ g₂) =
      qC (sl hmM' γ hγ f₂) * qC (sl hmM' γ hγ g) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hne := qC_sl_ne_zero hmM' γ hγ hg₂
  apply mul_right_cancel₀ hne
  calc w' * qC (sl hmM' γ hγ g) * qC (sl hmM' γ hγ g₂)
      = w' * qC (sl hmM' γ hγ g₂) * qC (sl hmM' γ hγ g) := by ring
    _ = qC (sl hmM' γ hγ f₂) * qC (sl hmM' γ hγ g) := by rw [hy]
    _ = qC (sl hmM' γ hγ f) * qC (sl hmM' γ hγ g₂) := hqs.symm

theorem IsImgC.unique {w y y' : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ w y) (h' : IsImgC hmM' γ hγ w y') :
    y = y' := by
  obtain ⟨k, f, g, hg, hw, hy'⟩ := h'
  have hy := h.apply_rep f g hg hw
  rw [← hy'] at hy
  exact mul_right_cancel₀ (qC_sl_ne_zero hmM' γ hγ hg) hy

theorem IsImgC.hasRep {w y : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ w y) :
    ∃ (k : ℤ) (f g : ModularForm (Γ m M') k), g ≠ 0 ∧ w = qC f / qC g := by
  obtain ⟨k, f, g, hg, hw, _⟩ := h
  exact ⟨k, f, g, hg, hw⟩

theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ m M') k₁} {g₂ : ModularForm (Γ m M') k₂}
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) : g₁.mul g₂ ≠ 0 := by
  intro h
  have : qC (⇑(g₁.mul g₂)) = 0 := by rw [h, ModularForm.coe_zero, qC_zero]
  rw [ModularForm.coe_mul, qC_mul] at this
  rcases mul_eq_zero.mp this with e | e
  · exact h₁ ((qC_eq_zero_iff _).mp e)
  · exact h₂ ((qC_eq_zero_iff _).mp e)

theorem IsImgC.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hmM' γ hγ x₁ y₁) (h₂ : IsImgC hmM' γ hγ x₂ y₂) :
    IsImgC hmM' γ hγ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, hg₂, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, mul_ne_zero_form hg₁ hg₂, ?_, ?_⟩
  · rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul, div_mul_div_comm]
  · rw [sl_mul_apply, sl_mul_apply, qC_mul, qC_mul, ← hy₁, ← hy₂]
    ring

theorem IsImgC.add {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hmM' γ hγ x₁ y₁) (h₂ : IsImgC hmM' γ hγ x₂ y₂) :
    IsImgC hmM' γ hγ (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, hg₂, rfl, hy₂⟩ := h₂
  have hg₁' : qC g₁ ≠ 0 := fun e => hg₁ ((qC_eq_zero_iff g₁).mp e)
  have hg₂' : qC g₂ ≠ 0 := fun e => hg₂ ((qC_eq_zero_iff g₂).mp e)
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, mul_ne_zero_form hg₁ hg₂, ?_, ?_⟩
  · rw [ModularForm.coe_add, qC_add, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul, qC_mul,
      qC_mul, qC_mul, div_add_div _ _ hg₁' hg₂']
  · rw [sl_add, ModularForm.coe_add, qC_add, sl_mul_apply, sl_mul_apply,
      sl_mul_apply, qC_mul, qC_mul, qC_mul, ← hy₁, ← hy₂]
    ring

theorem IsImgC.neg {x y : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ x y) : IsImgC hmM' γ hγ (-x) (-y) := by
  obtain ⟨k, f, g, hg, rfl, hy⟩ := h
  refine ⟨k, -f, g, hg, ?_, ?_⟩
  · rw [ModularForm.coe_neg, qC_neg]
    exact (neg_div (qC ⇑g) (qC ⇑f)).symm
  · rw [sl_neg, qC_neg, ← hy]
    ring

theorem one_ne_zero_form : (1 : ModularForm (Γ m M') 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm (Γ m M') 0 => qC (⇑F)) h
  simp only [ModularForm.one_coe_eq_one, qC_one, ModularForm.coe_zero, qC_zero] at this
  exact one_ne_zero this

theorem IsImgC.const (c : ℂ) : IsImgC hmM' γ hγ (HahnSeries.C c) (HahnSeries.C c) := by
  refine ⟨0, ModularForm.const c, 1, one_ne_zero_form, ?_, ?_⟩
  · rw [qC_const, ModularForm.one_coe_eq_one, qC_one, div_one]
  · have h1 : sl hmM' γ hγ (1 : ModularForm (Γ m M') 0) = 1 := by
      have := sl_const hmM' γ hγ (1 : ℂ)
      have e : (ModularForm.const 1 : ModularForm (Γ m M') 0) = 1 := by
        ext τ; simp
      rwa [e] at this
    rw [h1, sl_const, ModularForm.one_coe_eq_one, qC_one, mul_one, qC_const]

theorem IsImgC.one : IsImgC hmM' γ hγ 1 1 := by
  simpa using IsImgC.const (hmM' := hmM') (γ := γ) (hγ := hγ) 1

theorem IsImgC.zero : IsImgC hmM' γ hγ 0 0 := by
  simpa using IsImgC.const (hmM' := hmM') (γ := γ) (hγ := hγ) 0

theorem IsImgC.inv {x y : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ x y) : IsImgC hmM' γ hγ x⁻¹ y⁻¹ := by
  obtain ⟨k, f, g, hg, rfl, hy⟩ := h
  by_cases hf : f = 0
  · have hy0 : y = 0 := by
      rw [hf, sl_zero, ModularForm.coe_zero, qC_zero] at hy
      exact (mul_eq_zero.mp hy).resolve_right (qC_sl_ne_zero hmM' γ hγ hg)
    rw [hf, ModularForm.coe_zero, qC_zero, zero_div, _root_.inv_zero, hy0, _root_.inv_zero]
    exact IsImgC.zero
  · refine ⟨k, g, f, hf, ?_, ?_⟩
    · rw [inv_div]
    · have hy' : y ≠ 0 := by
        intro e
        rw [e, zero_mul] at hy
        exact qC_sl_ne_zero hmM' γ hγ hf hy.symm
      rw [← hy, inv_mul_cancel_left₀ hy']

theorem IsImgC.symm {x y : LaurentSeries ℂ} (h : IsImgC hmM' γ hγ x y)
    (hyS : ∃ (k : ℤ) (P Q : ModularForm (Γ m M') k), Q ≠ 0 ∧ y = qC P / qC Q) :
    IsImgC hmM' γ⁻¹ (inv_mem hγ) y x := by
  obtain ⟨k, f, g, hg, hx, hy⟩ := h
  obtain ⟨kP, P, Q, hQ, rfl⟩ := hyS
  refine ⟨kP, P, Q, hQ, rfl, ?_⟩
  have hQ' : qC Q ≠ 0 := fun e => hQ ((qC_eq_zero_iff Q).mp e)
  have h1 : qC P * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f) * qC Q := by
    rw [← hy, div_mul_eq_mul_div, div_mul_cancel₀ _ hQ']
  have hfun := mul_eq_mul_of_qC P (sl hmM' γ hγ g) (sl hmM' γ hγ f) Q (add_comm k kP) h1
  have hsl := slash_mul_eq hmM' P (sl hmM' γ hγ g) (sl hmM' γ hγ f) Q (add_comm k kP) hfun γ⁻¹ (inv_mem hγ)
  rw [sl_inv_sl, sl_inv_sl] at hsl
  have hq : qC (sl hmM' γ⁻¹ (inv_mem hγ) P) * qC g = qC f * qC (sl hmM' γ⁻¹ (inv_mem hγ) Q) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hg' : qC g ≠ 0 := fun e => hg ((qC_eq_zero_iff g).mp e)
  rw [hx, div_mul_eq_mul_div, div_eq_iff hg']
  exact hq.symm

theorem IsImgC.congr_γ {γ' : SL(2, ℤ)} (e : γ = γ') {hγ' : γ' ∈ Gamma0 M'} {x y : LaurentSeries ℂ}
    (h : IsImgC hmM' γ hγ x y) : IsImgC hmM' γ' hγ' x y := by
  subst e; exact h

end Img
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Emb

abbrev KL (L : Type) [Field L] [CharZero L] (m M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') (levelH m M'))

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

private abbrev _root_.W1xLA.ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

p2m_export "W1xLA" "ιB"
omit [NeZero m] in
private theorem _root_.W1xLA.ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

p2m_export "W1xLA" "ιB_injective"
omit [NeZero m] in
theorem ιB_coeffEmb (x : LaurentSeries ℚ) : ιB ι₀ (coeffEmb L x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

omit [NeZero m] in
theorem ιB_C (c : L) : ιB ι₀ (HahnSeries.C c) = HahnSeries.C (ι₀ c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

omit [NeZero m] in
theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

omit [NeZero m] in
theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ne_zero_of_intSeriesC {k : ℤ} {g : ModularForm (Γ m M') k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ m M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

end Emb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Gen

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ξ : L)

abbrev eq (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

omit [NeZero m] in

theorem exists_ratCast_of_isIntegralQExp {φ : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp φ p) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 φ).coeff n = (r : ℂ) :=
  ⟨((PowerSeries.coeff n p : ℤ) : ℚ), by rw [← h.coeff n]; push_cast; rfl⟩

def res1 {k : ℤ} (g : ModularForm (Γ m M') k) :
    ModularForm ((Gamma1 (m ^ 2 * M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_GammaH _ _)) g

omit [NeZero m] in
@[scoped simp] theorem coe_res1 {k : ℤ} (g : ModularForm (Γ m M') k) : (⇑(res1 g) : ℍ → ℂ) = g := rfl

theorem exists_isIntegralQExp_smul {k : ℤ} (g : ModularForm (Γ m M') k)
    (hg : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ, IsIntegralQExp ((D : ℂ) • (⇑g : ℍ → ℂ)) p := by
  obtain ⟨D, p, hD, hp⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (m ^ 2 * M') (res1 g) hg
  exact ⟨D, hD, p, hp⟩

omit [NeZero m] in

theorem isIntegralQExp_smul_of_dvd {k : ℤ} (g : ModularForm (Γ m M') k) {D₁ D : ℤ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D₁ : ℂ) • (⇑g : ℍ → ℂ)) p) {e : ℤ} (he : D = D₁ * e) :
    IsIntegralQExp (⇑((D : ℂ) • g) : ℍ → ℂ) (PowerSeries.C e * p) := by
  rw [IsIntegralQExp] at hp ⊢
  have h1 : (⇑((D : ℂ) • g) : ℍ → ℂ) = (e : ℂ) • (⇑((D₁ : ℂ) • g) : ℍ → ℂ) := by
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, smul_smul, he]
    push_cast
    rw [mul_comm]
  rw [h1, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods (e : ℂ) ((D₁ : ℂ) • g),
    ModularForm.IsGLPos.coe_smul, ← hp, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]
  rfl

include hmM' hγ in

theorem child {k : ℤ} (hk : Even k) (f : ModularForm (Γ m M') k) (pf : PowerSeries ℤ) (hf : IsIntegralQExp f pf) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ (h : ℕ → ModularForm (Γ m M') k) (p : ℕ → PowerSeries ℤ),
      (∀ j : ℕ, IsIntegralQExp (h j) (p j)) ∧
        (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(h j) : ℍ → ℂ) := by
  classical

  obtain ⟨hr, hrat, hrec⟩ :=
    ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0 m M' hmM' hk f
      (exists_ratCast_of_isIntegralQExp hf) γ hγ

  have hBD : ∀ j : ℕ, ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ,
      IsIntegralQExp ((D : ℂ) • (⇑(hr j) : ℍ → ℂ)) p :=
    fun j => exists_isIntegralQExp_smul (hr j) (hrat j)
  choose D hD0 p hp using hBD

  set Dt : ℤ := ∏ j ∈ Finset.range m, D j with hDt
  have hDt0 : Dt ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hD0 j
  have hdvd : ∀ j ∈ Finset.range m, D j ∣ Dt := fun j hj => Finset.dvd_prod_of_mem D hj
  have hmat : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] := by
    have : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] = 1 := by
      rw [Nat.cast_one]; exact (Matrix.one_fin_two).symm
    rw [this, one_mul, mul_one]
  refine ⟨Dt, hDt0, fun j => if j < m then (Dt : ℂ) • hr j else 0,
    fun j => if j < m then PowerSeries.C (Dt / D j) * p j else 0, ?_, ?_⟩
  · intro j
    by_cases hj : j < m
    · simp only [if_pos hj]
      obtain ⟨e, he⟩ := hdvd j (Finset.mem_range.mpr hj)
      have hediv : Dt / D j = e := by rw [he, Int.mul_ediv_cancel_left _ (hD0 j)]
      rw [hediv]
      exact isIntegralQExp_smul_of_dvd (hr j) (hp j) he
    · simp only [if_neg hj]
      rw [ModularForm.coe_zero]
      exact ModularCurve.isIntegralQExp_zero
  · rw [hrec 1 γ (Nat.coprime_one_left m) hγ hmat, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (Finset.mem_range.mp hj), ModularForm.IsGLPos.coe_smul]
    rw [smul_comm]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

theorem isIntegralQExp_mul {k₁ k₂ : ℤ} {f : ModularForm (Γ m M') k₁} {g : ModularForm (Γ m M') k₂}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g).symm

include hmM' hγ in

theorem evenRep {k : ℤ} (f g : ModularForm (Γ m M') k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    g.mul g ≠ 0 ∧ IsIntegralQExp (g.mul g) (pg * pg) ∧ intSeriesC ℚ (pg * pg) ≠ 0 ∧
      ιC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC (f.mul g) / qC (g.mul g) ∧
      ∃ (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧ ∃ (hF hG : ℕ → ModularForm (Γ m M') (k + k)) (pF pG : ℕ → PowerSeries ℤ),
        (∀ j : ℕ, IsIntegralQExp (hF j) (pF j)) ∧ (∀ j : ℕ, IsIntegralQExp (hG j) (pG j)) ∧
        (Df : ℂ) • ((⇑(f.mul g) : ℍ → ℂ) ∣[k + k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(hF j) : ℍ → ℂ) ∧
        (Dg : ℂ) • ((⇑(g.mul g) : ℍ → ℂ) ∣[k + k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(hG j) : ℍ → ℂ) := by
  have hg' : g ≠ 0 := ne_zero_of_intSeriesC_ne_zero hg hg0
  have hkk : Even (k + k) := ⟨k, rfl⟩
  obtain ⟨Df, hDf, hF, pF, hpF, hallF⟩ := child hmM' γ hγ hkk (f.mul g) (pf * pg) (isIntegralQExp_mul hf hg)
  obtain ⟨Dg, hDg, hG, pG, hpG, hallG⟩ := child hmM' γ hγ hkk (g.mul g) (pg * pg) (isIntegralQExp_mul hg hg)
  refine ⟨mul_ne_zero_form hg' hg', isIntegralQExp_mul hg hg, ?_, ?_, Df, Dg, hDf, hDg, hF, hG, pF, pG, hpF, hpG,
    hallF, hallG⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0
  · have hqg : qC g ≠ 0 := qC_ne_zero_of_intSeriesC hg hg0
    rw [map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul,
      mul_div_mul_right _ _ hqg]

variable (m) in

def twist (p : ℕ → PowerSeries ℤ) : LaurentSeries L :=
  ∑ j ∈ Finset.range m, HahnSeries.C (ξ ^ j) * coeffEmb L (intSeriesC ℚ (p j))

theorem coeffMap_twist (ι : L →+* ℂ) (hι : ι ξ = eq m) {k : ℤ} (f : ModularForm (Γ m M') k)
    {D : ℤ} {h : ℕ → ModularForm (Γ m M') k} {p : ℕ → PowerSeries ℤ} (hp : ∀ j : ℕ, IsIntegralQExp (h j) (p j))
    (hall : (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(h j) : ℍ → ℂ)) :
    coeffMap ι (twist m ξ p) = HahnSeries.C (D : ℂ) * qC (sl hmM' γ hγ f) := by
  rw [twist, map_sum]
  have e1 : ∀ j ∈ Finset.range m, coeffMap ι (HahnSeries.C (ξ ^ j) * coeffEmb L (intSeriesC ℚ (p j))) =
      HahnSeries.C ((eq m) ^ j) * qC (h j) := fun j _ => by
    rw [map_mul, ← ιC_intSeriesC (hp j), ← ιB_coeffEmb ι, ιB_C, map_pow, hι]
  rw [Finset.sum_congr rfl e1, ← qC_sum_smul, ← hall, ← coe_sl hmM' γ hγ, qC_smul]

variable (m) in

def genImg (Df Dg : ℤ) (pF pG : ℕ → PowerSeries ℤ) : LaurentSeries L :=
  (HahnSeries.C (Dg : L) * twist m ξ pF) / (HahnSeries.C (Df : L) * twist m ξ pG)

theorem coeffMap_genImg_mul (ι : L →+* ℂ) (hι : ι ξ = eq m) {k : ℤ} (f g : ModularForm (Γ m M') k)
    (hg : g ≠ 0) {Df Dg : ℤ} (hDf : Df ≠ 0) (hDg : Dg ≠ 0)
    {hF hG : ℕ → ModularForm (Γ m M') k} {pF pG : ℕ → PowerSeries ℤ}
    (hpF : ∀ j : ℕ, IsIntegralQExp (hF j) (pF j)) (hpG : ∀ j : ℕ, IsIntegralQExp (hG j) (pG j))
    (hallF : (Df : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(hF j) : ℍ → ℂ))
    (hallG : (Dg : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] conjElemN m γ) = ∑ j ∈ Finset.range m, (eq m) ^ j • (⇑(hG j) : ℍ → ℂ)) :
    coeffMap ι (genImg m ξ Df Dg pF pG) * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f) := by
  rw [genImg, map_div₀, map_mul, map_mul, coeffMap_twist hmM' γ hγ ξ ι hι f hpF hallF,
    coeffMap_twist hmM' γ hγ ξ ι hι g hpG hallG, ιB_C, ιB_C, map_intCast ι Df, map_intCast ι Dg]
  have hDf' : (HahnSeries.C (Df : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDf)
  have hDg' : (HahnSeries.C (Dg : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDg)
  have hv : qC (sl hmM' γ hγ g) ≠ 0 := qC_sl_ne_zero hmM' γ hγ hg
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hDf' (mul_ne_zero hDg' hv))]
  ring

theorem genImg_mem {k : ℤ} (g : ModularForm (Γ m M') k) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (Df Dg : ℤ)
    {hF hG : ℕ → ModularForm (Γ m M') k} {pF pG : ℕ → PowerSeries ℤ}
    (hpF : ∀ j : ℕ, IsIntegralQExp (hF j) (pF j)) (hpG : ∀ j : ℕ, IsIntegralQExp (hG j) (pG j)) :
    genImg m ξ Df Dg pF pG ∈ KL L m M' := by
  set E : LaurentSeries L := coeffEmb L (intSeriesC ℚ pg) with hE
  have hE0 : E ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0
  have htw : ∀ {hX : ℕ → ModularForm (Γ m M') k} {pX : ℕ → PowerSeries ℤ},
      (∀ j : ℕ, IsIntegralQExp (hX j) (pX j)) → twist m ξ pX / E ∈ KL L m M' := by
    intro hX pX hpX
    rw [twist, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc, hE, ← map_div₀]
    refine mul_mem ?_ (coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC (hX j) g (hpX j) hg hg0))
    rw [C_eq_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  have e : genImg m ξ Df Dg pF pG =
      (HahnSeries.C (Dg : L) * (twist m ξ pF / E)) / (HahnSeries.C (Df : L) * (twist m ξ pG / E)) := by
    rw [genImg, ← mul_div_assoc, ← mul_div_assoc, div_div_div_cancel_right₀ hE0]
  rw [e]
  refine div_mem (mul_mem ?_ (htw hpF)) (mul_mem ?_ (htw hpG)) <;>
  · rw [C_eq_algebraMap]; exact IntermediateField.algebraMap_mem _ _

end Gen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Good

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ξ : L)
  (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)

def Good (X : LaurentSeries L) : Prop :=
  X ∈ KL L m M' ∧ ∃ Y ∈ KL L m M', IsImgC hmM' γ hγ (ιB ι₀ X) (ιB ι₀ Y)

variable {hmM' γ hγ ι₀}

theorem Good.mul {X₁ X₂ : LaurentSeries L} (h₁ : Good hmM' γ hγ ι₀ X₁) (h₂ : Good hmM' γ hγ ι₀ X₂) :
    Good hmM' γ hγ ι₀ (X₁ * X₂) := by
  obtain ⟨hX₁, Y₁, hY₁, i₁⟩ := h₁
  obtain ⟨hX₂, Y₂, hY₂, i₂⟩ := h₂
  exact ⟨mul_mem hX₁ hX₂, Y₁ * Y₂, mul_mem hY₁ hY₂, by rw [map_mul, map_mul]; exact i₁.mul i₂⟩

theorem Good.add {X₁ X₂ : LaurentSeries L} (h₁ : Good hmM' γ hγ ι₀ X₁) (h₂ : Good hmM' γ hγ ι₀ X₂) :
    Good hmM' γ hγ ι₀ (X₁ + X₂) := by
  obtain ⟨hX₁, Y₁, hY₁, i₁⟩ := h₁
  obtain ⟨hX₂, Y₂, hY₂, i₂⟩ := h₂
  exact ⟨add_mem hX₁ hX₂, Y₁ + Y₂, add_mem hY₁ hY₂, by rw [map_add, map_add]; exact i₁.add i₂⟩

theorem Good.neg {X : LaurentSeries L} (h : Good hmM' γ hγ ι₀ X) : Good hmM' γ hγ ι₀ (-X) := by
  obtain ⟨hX, Y, hY, i⟩ := h
  exact ⟨neg_mem hX, -Y, neg_mem hY, by rw [map_neg, map_neg]; exact i.neg⟩

theorem Good.inv {X : LaurentSeries L} (h : Good hmM' γ hγ ι₀ X) : Good hmM' γ hγ ι₀ X⁻¹ := by
  obtain ⟨hX, Y, hY, i⟩ := h
  exact ⟨inv_mem hX, Y⁻¹, inv_mem hY, by rw [map_inv₀, map_inv₀]; exact i.inv⟩

theorem Good.one : Good hmM' γ hγ ι₀ 1 :=
  ⟨one_mem _, 1, one_mem _, by rw [map_one]; exact IsImgC.one⟩

theorem good_algebraMap (c : L) : Good hmM' γ hγ ι₀ (algebraMap L (LaurentSeries L) c) := by
  refine ⟨IntermediateField.algebraMap_mem _ _, algebraMap L (LaurentSeries L) c,
    IntermediateField.algebraMap_mem _ _, ?_⟩
  rw [← C_eq_algebraMap, ιB_C]
  exact IsImgC.const _

include hι₀ in

theorem Good.gen {x : LaurentSeries ℚ} (hx : x ∈ intFormRatiosC ℚ (GH m M')) :
    Good hmM' γ hγ ι₀ (coeffEmb L x) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨hG', hGG, hGG0, hrep, Df, Dg, hDf, hDg, hF, hG, pF, pG, hpF, hpG, hallF, hallG⟩ :=
    evenRep hmM' γ hγ f g pf pg hf hg hg0
  refine ⟨coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hg0),
    genImg m ξ Df Dg pF pG, genImg_mem ξ (g.mul g) (pg * pg) hGG hGG0 Df Dg hpF hpG, k + k, f.mul g, g.mul g, hG',
    ?_, ?_⟩
  · rw [ιB_coeffEmb, hrep]
  · exact coeffMap_genImg_mul hmM' γ hγ ξ ι₀ hι₀ (f.mul g) (g.mul g) hG' hDf hDg hpF hpG hallF hallG

include hι₀ in

theorem Good.of_mem_field {x : LaurentSeries ℚ} (hx : x ∈ xHFunctionField (m ^ 2 * M') (levelH m M')) :
    Good hmM' γ hγ ι₀ (coeffEmb L x) := by
  change x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M')) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact good_algebraMap _
      · exact Good.gen ξ hι₀ hy
  | one => rw [map_one]; exact Good.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

include hι₀ in

theorem Good.of_mem {X : LaurentSeries L} (hX : X ∈ KL L m M') : Good hmM' γ hγ ι₀ X := by
  rw [mem_laurentBaseChange_iff] at hX
  induction hX using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact good_algebraMap c
      · exact Good.of_mem_field ξ hι₀ hz
  | one => exact Good.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Good
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Auto

variable (hmM' : Nat.Coprime m M') (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)
  (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def Φfun (X : KL L m M') : KL L m M' :=
  ⟨Classical.choose (Good.of_mem ξ hι₀ (hmM' := hmM') (γ := γ) (hγ := hγ) X.2).2,
    (Classical.choose_spec (Good.of_mem ξ hι₀ (hmM' := hmM') (γ := γ) (hγ := hγ) X.2).2).1⟩

theorem isImgC_Φfun (X : KL L m M') :
    IsImgC hmM' γ hγ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ (Φfun hmM' ξ ι₀ hι₀ γ hγ X)) :=
  (Classical.choose_spec (Good.of_mem ξ hι₀ (hmM' := hmM') (γ := γ) (hγ := hγ) X.2).2).2

theorem Φfun_eq {X : KL L m M'} {Y : LaurentSeries L}
    (h : IsImgC hmM' γ hγ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ Y)) :
    (Φfun hmM' ξ ι₀ hι₀ γ hγ X : LaurentSeries L) = Y :=
  ιB_injective ι₀ ((isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X).unique h)

def ΦHom : KL L m M' →+* KL L m M' where
  toFun := Φfun hmM' ξ ι₀ hι₀ γ hγ
  map_one' := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [OneMemClass.coe_one, map_one]; exact IsImgC.one))
  map_mul' X Y := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [MulMemClass.coe_mul, map_mul]
    exact (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X).mul (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ Y)))
  map_zero' := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [ZeroMemClass.coe_zero, map_zero]; exact IsImgC.zero))
  map_add' X Y := Subtype.ext (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (by
    simp only [AddMemClass.coe_add, map_add]
    exact (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X).add (isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ Y)))

theorem ΦHom_apply (X : KL L m M') : ΦHom hmM' ξ ι₀ hι₀ γ hγ X = Φfun hmM' ξ ι₀ hι₀ γ hγ X := rfl

theorem isImgC_ΦHom (X : KL L m M') :
    IsImgC hmM' γ hγ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ (ΦHom hmM' ξ ι₀ hι₀ γ hγ X)) :=
  isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ X

theorem ΦHom_algebraMap (c : L) :
    ΦHom hmM' ξ ι₀ hι₀ γ hγ (algebraMap L (KL L m M') c) = algebraMap L (KL L m M') c := by
  apply Subtype.ext
  refine Φfun_eq hmM' ξ ι₀ hι₀ γ hγ ?_
  show IsImgC hmM' γ hγ (ιB ι₀ (algebraMap L (LaurentSeries L) c)) (ιB ι₀ (algebraMap L (LaurentSeries L) c))
  rw [← C_eq_algebraMap, ιB_C]
  exact IsImgC.const _

theorem ΦHom_inv_apply (X : KL L m M') :
    ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) (ΦHom hmM' ξ ι₀ hι₀ γ hγ X) = X := by
  apply Subtype.ext
  refine Φfun_eq hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) ?_
  exact (isImgC_ΦHom hmM' ξ ι₀ hι₀ γ hγ X).symm
    (isImgC_ΦHom hmM' ξ ι₀ hι₀ γ hγ (ΦHom hmM' ξ ι₀ hι₀ γ hγ X)).hasRep

theorem ΦHom_apply_inv (X : KL L m M') :
    ΦHom hmM' ξ ι₀ hι₀ γ hγ (ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X) = X := by
  apply Subtype.ext
  refine Φfun_eq hmM' ξ ι₀ hι₀ γ hγ ?_
  exact ((isImgC_ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X).symm
    (isImgC_ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) (ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ) X)).hasRep).congr_γ
    (inv_inv γ)

def ΦRingEquiv : KL L m M' ≃+* KL L m M' :=
  { ΦHom hmM' ξ ι₀ hι₀ γ hγ with
    invFun := ΦHom hmM' ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ)
    left_inv := ΦHom_inv_apply hmM' ξ ι₀ hι₀ γ hγ
    right_inv := ΦHom_apply_inv hmM' ξ ι₀ hι₀ γ hγ }

def τEquiv : KL L m M' ≃ₐ[L] KL L m M' :=
  AlgEquiv.ofRingEquiv (f := ΦRingEquiv hmM' ξ ι₀ hι₀ γ hγ) (ΦHom_algebraMap hmM' ξ ι₀ hι₀ γ hγ)

theorem τEquiv_apply (X : KL L m M') : τEquiv hmM' ξ ι₀ hι₀ γ hγ X = Φfun hmM' ξ ι₀ hι₀ γ hγ X := rfl

theorem isLevelAutAt_τEquiv :
    IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') γ (KL L m M') (τEquiv hmM' ξ ι₀ hι₀ γ hγ) := by
  intro k f g pf pg hf hg hg0 x hx ι hι
  obtain ⟨hG', hGG, hGG0, hrep, Df, Dg, hDf, hDg, hF, hG, pF, pG, hpF, hpG, hallF, hallG⟩ :=
    evenRep hmM' γ hγ f g pf pg hf hg hg0
  have hval : (τEquiv hmM' ξ ι₀ hι₀ γ hγ x : LaurentSeries L) = genImg m ξ Df Dg pF pG := by
    rw [τEquiv_apply]
    refine Φfun_eq hmM' ξ ι₀ hι₀ γ hγ ⟨k + k, f.mul g, g.mul g, hG', ?_, ?_⟩
    · rw [hx, ιB_coeffEmb, hrep]
    · exact coeffMap_genImg_mul hmM' γ hγ ξ ι₀ hι₀ (f.mul g) (g.mul g) hG' hDf hDg hpF hpG hallF hallG
  rw [hval]

  have h2 := coeffMap_genImg_mul hmM' γ hγ ξ ι hι (f.mul g) (g.mul g) hG' hDf hDg hpF hpG hallF hallG
  rw [sl_mul_apply, sl_mul_apply, qC_mul, qC_mul, ← mul_assoc] at h2
  exact mul_right_cancel₀ (qC_sl_ne_zero hmM' γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0)) h2

end Auto
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Emb0

variable (L : Type) [Field L] [CharZero L]

theorem exists_emb [IsCyclotomicExtension {m} ℚ L] (ξ : L) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι₀ : L →+* ℂ, ι₀ ξ = eq m := by
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite_of_singleton (n := m) ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (mpos m)).symm
  have hroot : eq m ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

end Emb0
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

theorem main (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ τ : ↥(KL L (q * ℓ) M') ≃ₐ[L] ↥(KL L (q * ℓ) M'),
      IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L (q * ℓ) M') τ := by
  have hcop : Nat.Coprime (q * ℓ) M' :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM')
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM')
  obtain ⟨ι₀, hι₀⟩ := exists_emb (m := q * ℓ) L ξ hξ
  exact ⟨τEquiv hcop ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ), isLevelAutAt_τEquiv hcop ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ)⟩

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

open scoped MatrixGroups ModularForm Manifold
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R4GC

section Group

variable (m : ℕ) [NeZero m]

theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

abbrev Dr : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix m

@[scoped simp] theorem Dr_coe : ((Dr m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] :=
  ModularForm.val_heckeDiagMatrix (NeZero.ne m)

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr m * conjElemN m γ = (γ : GL (Fin 2) ℝ) * Dr m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (mne m), mul_comm]

theorem conjElemN_eq (γ : SL(2, ℤ)) : conjElemN m γ = (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

def shp : SL(2, ℤ) →* GL (Fin 2) ℝ where
  toFun γ := conjElemN m γ
  map_one' := by simp only [conjElemN_eq, map_one]; group
  map_mul' γ δ := by simp only [conjElemN_eq, map_mul]; group

@[scoped simp] theorem shp_apply (γ : SL(2, ℤ)) : shp m γ = conjElemN m γ := rfl

theorem conjElemN_mul (γ δ : SL(2, ℤ)) : conjElemN m (γ * δ) = conjElemN m γ * conjElemN m δ :=
  map_mul (shp m) γ δ

theorem conjElemN_inv (γ : SL(2, ℤ)) : conjElemN m γ⁻¹ = (conjElemN m γ)⁻¹ := map_inv (shp m) γ

theorem coeGL_injective : Function.Injective (fun γ : SL(2, ℤ) => (γ : GL (Fin 2) ℝ)) := by
  intro γ δ h
  ext i j
  have := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

theorem shp_injective : Function.Injective (shp m) := by
  intro γ δ h
  simp only [shp_apply, conjElemN_eq, mul_left_inj, mul_right_inj] at h
  exact coeGL_injective h

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext; simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElemN_val (γ : SL(2, ℤ)) : ((conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

variable {m}

def upMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, (m : ℤ) * δ 0 1; δ 1 0 / m, δ 1 1]

theorem det_upMat (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : (upMat (m := m) δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def upSL (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨upMat (m := m) δ, det_upMat δ h⟩

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / m; (m : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : (downMat (m := m) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (m := m) ε, det_downMat ε h⟩

theorem upSL_coe (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) :
    ((upSL δ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr m = Dr m * (δ : GL (Fin 2) ℝ) := by
  obtain ⟨c, hc⟩ := h
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upSL, upMat, hc, h1] <;> ring

theorem downSL_coe (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    Dr m * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr m := by
  obtain ⟨b, hb⟩ := h
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

theorem conjElemN_upSL (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : conjElemN m (upSL δ h) = (δ : GL (Fin 2) ℝ) := by
  rw [conjElemN_eq, mul_assoc, upSL_coe, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conjElemN_eq_downSL' (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    conjElemN m ε = ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [conjElemN_eq, mul_assoc, ← downSL_coe ε h, inv_mul_cancel_left]

variable (m) (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Δ : Subgroup SL(2, ℤ) := Gamma m ⊓ Gamma0 M'

variable {m M'}

theorem mem_Δ_iff {δ : SL(2, ℤ)} : δ ∈ Δ m M' ↔ δ ∈ Gamma m ∧ δ ∈ Gamma0 M' := Subgroup.mem_inf

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

scoped instance GH_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] : (GH m M').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

omit [NeZero m] in
theorem m_dvd_level : (m : ℤ) ∣ ((m ^ 2 * M' : ℕ) : ℤ) := ⟨m * M', by push_cast; ring⟩

theorem m_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans m_dvd_level h10

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact m_dvd_lowerLeft_of_mem_GH hδ
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem upSL_mem_Δ {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : upSL δ (m_dvd_lowerLeft_of_mem_GH hδ) ∈ Δ m M' := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  have hquot : δ 1 0 / (m : ℤ) = m * (M' * c) := by
    rw [hc]; push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  refine mem_Δ_iff.mpr ⟨?_, ?_⟩
  · rw [Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ((δ 0 0 : ℤ) : ZMod m) = 1
      exact upperLeft_of_mem_GH hδ
    · show (((m : ℤ) * δ 0 1 : ℤ) : ZMod m) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
    · show ((δ 1 0 / m : ℤ) : ZMod m) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hquot]; exact Dvd.intro _ rfl
    · show ((δ 1 1 : ℤ) : ZMod m) = 1
      exact h11
  · rw [Gamma0_mem]
    show ((δ 1 0 / m : ℤ) : ZMod M') = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hquot]
    exact ⟨m * c, by ring⟩

theorem m_dvd_01_of_mem_Gamma {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma m) : (m : ℤ) ∣ δ 0 1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hδ).2.1

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem downSL_mem {δ : SL(2, ℤ)} (hδ : δ ∈ Δ m M') :
    downSL (m := m) δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1) ∈ GH m M' := by
  obtain ⟨-, -, h10, h11⟩ := Gamma_mem.mp (mem_Δ_iff.mp hδ).1
  rw [mem_GH_iff]
  refine ⟨?_, h11⟩
  show ((((m : ℤ) * δ 1 0 : ℤ)) : ZMod (m ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (m : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hM : (M' : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (mem_Δ_iff.mp hδ).2)
  have hcop : IsCoprime (m : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hmM'
  obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
  exact ⟨c, by rw [hc]; push_cast; ring⟩

theorem mem_Γ_iff_exists (A : GL (Fin 2) ℝ) : A ∈ Γ m M' ↔ ∃ δ ∈ Δ m M', conjElemN m δ = A := by
  constructor
  · rintro ⟨A', hA', rfl⟩
    exact ⟨upSL A' (m_dvd_lowerLeft_of_mem_GH hA'), upSL_mem_Δ hA', conjElemN_upSL _ _⟩
  · rintro ⟨δ, hδ, rfl⟩
    rw [conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1)]
    exact ⟨_, downSL_mem hmM' hδ, rfl⟩

theorem conj_mem_Γ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {A : GL (Fin 2) ℝ} (hA : A ∈ Γ m M') :
    conjElemN m γ * A * (conjElemN m γ)⁻¹ ∈ Γ m M' := by
  obtain ⟨δ, hδ, rfl⟩ := (mem_Γ_iff_exists hmM' A).mp hA
  rw [← conjElemN_inv, ← conjElemN_mul, ← conjElemN_mul, mem_Γ_iff_exists hmM']
  refine ⟨γ * δ * γ⁻¹, mem_Δ_iff.mpr ⟨?_, ?_⟩, rfl⟩
  · exact (Gamma_normal m).conj_mem δ (mem_Δ_iff.mp hδ).1 γ
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ (mem_Δ_iff.mp hδ).2) (Subgroup.inv_mem _ hγ)

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ m M' ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' := by
  intro A hA
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  exact conj_mem_Γ hmM' hγ hA

end Group
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Frame

variable {n m : ℕ} [NeZero n] [NeZero m] {M' : ℕ}

theorem Gamma_le_of_dvd (h : n ∣ m) : Gamma m ≤ Gamma n := by
  intro δ hδ
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  have c0 : ∀ z : ℤ, ((z : ZMod m) = 0) → ((z : ZMod n) = 0) := fun z hz => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz ⊢; exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hz
  have c1 : ∀ z : ℤ, ((z : ZMod m) = 1) → ((z : ZMod n) = 1) := fun z hz => by
    have := congrArg (ZMod.castHom h (ZMod n)) hz
    rwa [map_intCast, map_one] at this
  exact Gamma_mem.mpr ⟨c1 _ h1, c0 _ h2, c0 _ h3, c1 _ h4⟩

theorem Δ_le_of_dvd (h : n ∣ m) : Δ m M' ≤ Δ n M' := fun δ hδ =>
  mem_Δ_iff.mpr ⟨Gamma_le_of_dvd h (mem_Δ_iff.mp hδ).1, (mem_Δ_iff.mp hδ).2⟩

variable (n m M') in

abbrev Hgp : Subgroup (GL (Fin 2) ℝ) := (Δ n M').map (shp m)

scoped instance : (Hgp n m M').HasDetOne :=
  ⟨by rintro _ ⟨δ, _, rfl⟩; exact det_conjElemN m δ⟩

theorem mem_Hgp_iff (A : GL (Fin 2) ℝ) : A ∈ Hgp n m M' ↔ ∃ δ ∈ Δ n M', conjElemN m δ = A := by
  simp [Hgp, Subgroup.mem_map]

variable (hmM' : Nat.Coprime m M') (hnm : n ∣ m)
include hmM' hnm

theorem Γ_le_Hgp : Γ m M' ≤ Hgp n m M' := fun A hA => by
  rw [mem_Hgp_iff]
  obtain ⟨δ, hδ, e⟩ := (mem_Γ_iff_exists hmM' A).mp hA
  exact ⟨δ, Δ_le_of_dvd hnm hδ, e⟩

theorem isFiniteRelIndex_Γ_Hgp [NeZero M'] : (Γ m M').IsFiniteRelIndex (Hgp n m M') := by
  have hle : (Gamma (m ^ 2 * M')).map (shp m) ≤ Γ m M' := by
    rintro _ ⟨δ, hδ, rfl⟩
    have hδ' : δ ∈ Δ m M' := by
      refine mem_Δ_iff.mpr ⟨Gamma_le_of_dvd ⟨m * M', by ring⟩ hδ, ?_⟩
      rw [Gamma0_mem]
      have h3 := (Gamma_mem.mp hδ).2.2.1
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢
      exact dvd_trans ⟨m ^ 2, by push_cast; ring⟩ h3
    rw [shp_apply, conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ').1)]
    exact ⟨_, downSL_mem hmM' hδ', rfl⟩
  haveI : NeZero (m ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (NeZero.ne m)) (NeZero.ne M')⟩
  haveI : ((Gamma (m ^ 2 * M')).map (shp m)).IsFiniteRelIndex (Hgp n m M') := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Hgp,
      Subgroup.relIndex_map_map_of_injective _ _ (shp_injective m)]
    haveI : (Gamma (m ^ 2 * M')).IsFiniteRelIndex (Δ n M') := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  exact Subgroup.isFiniteRelIndex_of_le_left (Hgp n m M') hle

end Frame
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Analytic

variable {m : ℕ} [NeZero m] {M' : ℕ}

section Slash

variable (hmM' : Nat.Coprime m M')
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) : ModularForm (Γ m M') k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_mul_coe {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ m M') k₁) (g : ModularForm (Γ m M') k₂) :
    ⇑(sl hmM' γ hγ (f.mul g)) = ⇑(sl hmM' γ hγ f) * ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElemN_val, abs_one, one_smul]

theorem sl_add_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ (f + g)) = ⇑(sl hmM' γ hγ f) + ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash]

theorem sl_neg_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ (-f)) = -⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

theorem sl_zero_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ⇑(sl hmM' γ hγ (0 : ModularForm (Γ m M') k)) = 0 := by
  simp only [coe_sl, ModularForm.coe_zero, SlashAction.zero_slash]

theorem sl_one_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ⇑(sl hmM' γ hγ (1 : ModularForm (Γ m M') 0)) = 1 := by
  funext τ
  simp only [coe_sl, ModularForm.one_coe_eq_one, ModularForm.slash_def, Pi.one_apply, σ_conjElemN_apply,
    det_conjElemN_val]
  simp

theorem sl_const_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    ⇑(sl hmM' γ hγ (ModularForm.const c : ModularForm (Γ m M') 0)) = ⇑(ModularForm.const c : ModularForm (Γ m M') 0) := by
  funext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElemN_apply,
    det_conjElemN_val]
  simp

theorem sl_sl_inv {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    sl hmM' γ⁻¹ (Subgroup.inv_mem _ hγ) (sl hmM' γ hγ f) = f := by
  ext τ
  simp only [coe_sl]
  rw [← SlashAction.slash_mul, ← conjElemN_mul, mul_inv_cancel, ← shp_apply, map_one, SlashAction.slash_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M') k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_sl_inv hmM' γ hγ f, h]
  ext τ
  simp [coe_sl]

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M') k₁) (g : ModularForm (Γ m M') k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g]

theorem qC_add {k : ℤ} (f g : ModularForm (Γ m M') k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ m M') k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ m M') k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ m M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ m M') 0) : ℍ → ℂ) = c • ((1 : ModularForm (Γ m M') 0) : ℍ → ℂ) := by
  funext z
  simp [ModularForm.one_coe_eq_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ m M') 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

theorem qC_coeff_neg (F : ℍ → ℂ) {n : ℤ} (hn : n < 0) : (qC F).coeff n = 0 :=
  ModularCurve.ofPowerSeries_coeff_of_neg _ hn

theorem qC_coeff_nat (F : ℍ → ℂ) (n : ℕ) : (qC F).coeff (n : ℤ) = (qExpansion 1 F).coeff n :=
  ofPowerSeries_apply_coeff _ _

theorem qC_sum_smul {k : ℤ} (s : Finset ℕ) (c : ℕ → ℂ) (h : ℕ → ModularForm (Γ m M') k) :
    qC (∑ j ∈ s, c j • (⇑(h j) : ℍ → ℂ)) = ∑ j ∈ s, HahnSeries.C (c j) * qC (h j) := by
  classical
  have hcoe : ∀ t : Finset ℕ, (∑ j ∈ t, c j • (⇑(h j) : ℍ → ℂ)) = ⇑(∑ j ∈ t, c j • h j) := fun t => by
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]
  induction s using Finset.induction_on with
  | empty => simp [qC_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hcoe t, ← ModularForm.IsGLPos.coe_smul, qC_add,
        ModularForm.IsGLPos.coe_smul, qC_smul, ← hcoe t, ih]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M') k₁) (f₂ : ModularForm (Γ m M') k₂)
    (f₃ : ModularForm (Γ m M') k₃) (f₄ : ModularForm (Γ m M') k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ m M') (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ m M') k₁} {g₂ : ModularForm (Γ m M') k₂}
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) : g₁.mul g₂ ≠ 0 := by
  intro h
  have : qC (⇑(g₁.mul g₂)) = 0 := by rw [h, ModularForm.coe_zero, qC_zero]
  rw [ModularForm.coe_mul, qC_mul] at this
  rcases mul_eq_zero.mp this with e | e
  · exact h₁ ((qC_eq_zero_iff _).mp e)
  · exact h₂ ((qC_eq_zero_iff _).mp e)

variable {L : Type} [Field L] [CharZero L]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

abbrev ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

theorem ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

theorem ιB_coeffEmb (x : LaurentSeries ℚ) : ιB ι₀ (coeffEmb L x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem ιB_algebraMap (c : L) : ιB ι₀ (algebraMap L (LaurentSeries L) c) = HahnSeries.C (ι₀ c) := by
  rw [← C_eq_algebraMap, HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) : ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

abbrev em (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

variable (L) in
theorem exists_emb [IsCyclotomicExtension {m} ℚ L] (ξ : L) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι₀ : L →+* ℂ, ι₀ ξ = em m := by
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite_of_singleton (n := m) ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : em m ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

def Efield : Subfield (LaurentSeries ℂ) := (ιB ι₀).fieldRange

theorem mem_Efield_iff (x : LaurentSeries ℂ) : x ∈ Efield ι₀ ↔ ∀ n : ℤ, x.coeff n ∈ Set.range ι₀ := by
  constructor
  · rintro ⟨y, rfl⟩ n
    exact ⟨y.coeff n, (coeffMap_coeff ι₀ y n).symm⟩
  · intro h
    have h0 : ∀ n, x.coeff n = 0 → (h n).choose = 0 := fun n hn => ι₀.injective (by
      rw [(h n).choose_spec, hn, map_zero])
    let y : LaurentSeries L :=
      { coeff := fun n => (h n).choose
        isPWO_support' := x.isPWO_support.mono (fun n hn => by
          intro hx
          exact hn (h0 n hx)) }
    refine ⟨y, ?_⟩
    ext n
    rw [coeffMap_coeff]
    exact (h n).choose_spec

def InE (F : ℍ → ℂ) : Prop := qC F ∈ Efield ι₀

theorem inE_iff (F : ℍ → ℂ) : InE ι₀ F ↔ ∀ n : ℕ, (qExpansion 1 F).coeff n ∈ Set.range ι₀ := by
  rw [InE, mem_Efield_iff]
  constructor
  · intro h n
    rw [← qC_coeff_nat]; exact h n
  · intro h n
    rcases lt_or_ge n 0 with hn | hn
    · rw [qC_coeff_neg _ hn]; exact ⟨0, map_zero _⟩
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [qC_coeff_nat]; exact h n

theorem C_mem_Efield (c : L) : (HahnSeries.C (ι₀ c) : LaurentSeries ℂ) ∈ Efield ι₀ :=
  ⟨HahnSeries.C c, by rw [HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]⟩

theorem ratCast_mem_range (r : ℚ) : (r : ℂ) ∈ Set.range ι₀ := ⟨r, map_ratCast ι₀ r⟩

theorem inE_sl_of_rat [NeZero M'] (hmM' : Nat.Coprime m M') {ξ : L} (hι₀ : ι₀ ξ = em m) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ m M') k) (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ))
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M') : InE ι₀ (sl hmM' ρ hρ f) := by
  obtain ⟨h, hrat, hslash⟩ :=
    ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0 m M' hmM' hk f hf ρ hρ
  have hcomm : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] * (ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
      = (ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] := by
    have : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this, Matrix.one_mul, Matrix.mul_one]
  have key := hslash 1 ρ (Nat.coprime_one_left m) hρ hcomm
  rw [InE, coe_sl, key, qC_sum_smul]
  refine Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ ?_ ?_
  ·
    have : Complex.exp (2 * Real.pi * Complex.I * ((1 * j : ℕ) : ℂ) / m) = (ι₀ ξ) ^ j := by
      rw [hι₀, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [this, ← map_pow]
    exact C_mem_Efield ι₀ _
  · rw [← InE, inE_iff]
    intro n
    obtain ⟨r, hr⟩ := hrat j n
    rw [hr]; exact ratCast_mem_range ι₀ r

end Analytic
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Good

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = em m)

abbrev KL (L : Type) [Field L] [CharZero L] (m : ℕ) (M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') (levelH m M'))

def Good (x : LaurentSeries L) : Prop :=
  x ∈ KL L m M' ∧
  ∃ (k : ℤ) (F G : ModularForm (Γ m M') k), G ≠ 0 ∧ ιB ι₀ x * qC G = qC F ∧
    (∀ (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M'), InE ι₀ (sl hmM' ρ hρ F) ∧ InE ι₀ (sl hmM' ρ hρ G)) ∧
    (∀ (hx : x ∈ KL L m M') (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M') (τ : KL L m M' ≃ₐ[L] KL L m M'),
      IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') ρ (KL L m M') τ →
        ιB ι₀ ((τ ⟨x, hx⟩ : KL L m M') : LaurentSeries L) * qC (sl hmM' ρ hρ G) = qC (sl hmM' ρ hρ F))

variable {hmM' ξ ι₀}

theorem Good.mem {x : LaurentSeries L} (h : Good hmM' ξ ι₀ x) : x ∈ KL L m M' := h.1

theorem one_form_ne_zero : (1 : ModularForm (Γ m M') 0) ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Γ m M') 0 => qC (⇑f)) h
  simp only [ModularForm.one_coe_eq_one, qC_one, ModularForm.coe_zero, qC_zero] at this
  exact one_ne_zero this

theorem Good.const (c : L) : Good hmM' ξ ι₀ (algebraMap L (LaurentSeries L) c) := by
  have hmem : algebraMap L (LaurentSeries L) c ∈ KL L m M' := IntermediateField.algebraMap_mem _ c
  refine ⟨hmem, 0, ModularForm.const (ι₀ c), 1, one_form_ne_zero, ?_, ?_, ?_⟩
  · rw [ιB_algebraMap, ModularForm.one_coe_eq_one, qC_one, mul_one, qC_const]
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [InE, sl_const_coe, qC_const]; exact C_mem_Efield ι₀ c
    · rw [InE, sl_one_coe, qC_one]; exact one_mem _
  · intro hx ρ hρ τ _
    have e : (⟨algebraMap L (LaurentSeries L) c, hx⟩ : KL L m M') = algebraMap L (KL L m M') c := Subtype.ext rfl
    rw [e, AlgEquiv.commutes, sl_const_coe, sl_one_coe, qC_one, mul_one, qC_const]
    exact ιB_algebraMap ι₀ c

theorem Good.zero : Good hmM' ξ ι₀ (0 : LaurentSeries L) := by
  have := Good.const (hmM' := hmM') (ξ := ξ) (ι₀ := ι₀) (0 : L)
  rwa [map_zero] at this

theorem Good.add {x y : LaurentSeries L} (hx : Good hmM' ξ ι₀ x) (hy : Good hmM' ξ ι₀ y) :
    Good hmM' ξ ι₀ (x + y) := by
  obtain ⟨hxm, k₁, F₁, G₁, hG₁, hxe, hxE, hxτ⟩ := hx
  obtain ⟨hym, k₂, F₂, G₂, hG₂, hye, hyE, hyτ⟩ := hy
  refine ⟨add_mem hxm hym, k₁ + k₂, F₁.mul G₂ + G₁.mul F₂, G₁.mul G₂, mul_ne_zero_form hG₁ hG₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_add, qC_add, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul, qC_mul,
      qC_mul, qC_mul, map_add]
    linear_combination qC G₂ * hxe + qC G₁ * hye
  · intro ρ hρ
    obtain ⟨hF₁, hG₁'⟩ := hxE ρ hρ
    obtain ⟨hF₂, hG₂'⟩ := hyE ρ hρ
    refine ⟨?_, ?_⟩
    · rw [InE, sl_add_coe, qC_add, sl_mul_coe, sl_mul_coe, qC_mul, qC_mul]
      exact add_mem (mul_mem hF₁ hG₂') (mul_mem hG₁' hF₂)
    · rw [InE, sl_mul_coe, qC_mul]
      exact mul_mem hG₁' hG₂'
  · intro hxy ρ hρ τ hτ
    have e : (⟨x + y, hxy⟩ : KL L m M') = ⟨x, hxm⟩ + ⟨y, hym⟩ := Subtype.ext rfl
    rw [e, map_add, IntermediateField.coe_add, map_add, sl_add_coe, qC_add, sl_mul_coe, sl_mul_coe, sl_mul_coe,
      qC_mul, qC_mul, qC_mul]
    linear_combination qC (sl hmM' ρ hρ G₂) * hxτ hxm ρ hρ τ hτ + qC (sl hmM' ρ hρ G₁) * hyτ hym ρ hρ τ hτ

theorem Good.neg {x : LaurentSeries L} (hx : Good hmM' ξ ι₀ x) : Good hmM' ξ ι₀ (-x) := by
  obtain ⟨hxm, k, F, G, hG, hxe, hxE, hxτ⟩ := hx
  refine ⟨neg_mem hxm, k, -F, G, hG, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_neg, qC_neg, map_neg, ← hxe]; ring
  · intro ρ hρ
    obtain ⟨hF, hG'⟩ := hxE ρ hρ
    refine ⟨?_, hG'⟩
    rw [InE, sl_neg_coe, qC_neg]; exact neg_mem hF
  · intro hx' ρ hρ τ hτ
    have e : (⟨-x, hx'⟩ : KL L m M') = -⟨x, hxm⟩ := Subtype.ext rfl
    rw [e, map_neg, IntermediateField.coe_neg, map_neg, sl_neg_coe, qC_neg, ← hxτ hxm ρ hρ τ hτ]; ring

theorem Good.mul {x y : LaurentSeries L} (hx : Good hmM' ξ ι₀ x) (hy : Good hmM' ξ ι₀ y) :
    Good hmM' ξ ι₀ (x * y) := by
  obtain ⟨hxm, k₁, F₁, G₁, hG₁, hxe, hxE, hxτ⟩ := hx
  obtain ⟨hym, k₂, F₂, G₂, hG₂, hye, hyE, hyτ⟩ := hy
  refine ⟨mul_mem hxm hym, k₁ + k₂, F₁.mul F₂, G₁.mul G₂, mul_ne_zero_form hG₁ hG₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul, map_mul]
    linear_combination ιB ι₀ y * qC G₂ * hxe + qC F₁ * hye
  · intro ρ hρ
    obtain ⟨hF₁, hG₁'⟩ := hxE ρ hρ
    obtain ⟨hF₂, hG₂'⟩ := hyE ρ hρ
    refine ⟨?_, ?_⟩
    · rw [InE, sl_mul_coe, qC_mul]; exact mul_mem hF₁ hF₂
    · rw [InE, sl_mul_coe, qC_mul]; exact mul_mem hG₁' hG₂'
  · intro hxy ρ hρ τ hτ
    have e : (⟨x * y, hxy⟩ : KL L m M') = ⟨x, hxm⟩ * ⟨y, hym⟩ := Subtype.ext rfl
    rw [e, map_mul, IntermediateField.coe_mul, map_mul, sl_mul_coe, sl_mul_coe, qC_mul, qC_mul]
    have h1 := hxτ hxm ρ hρ τ hτ
    have h2 := hyτ hym ρ hρ τ hτ
    linear_combination ιB ι₀ ((τ ⟨y, hym⟩ : KL L m M') : LaurentSeries L) * qC (sl hmM' ρ hρ G₂) * h1 +
      qC (sl hmM' ρ hρ F₁) * h2

theorem Good.inv {x : LaurentSeries L} (hx : Good hmM' ξ ι₀ x) : Good hmM' ξ ι₀ x⁻¹ := by
  by_cases hx0 : x = 0
  · rw [hx0, _root_.inv_zero]; exact Good.zero
  obtain ⟨hxm, k, F, G, hG, hxe, hxE, hxτ⟩ := hx
  have hιx : ιB ι₀ x ≠ 0 := (map_ne_zero_iff _ (ιB_injective ι₀)).mpr hx0
  have hF : F ≠ 0 := by
    intro hF
    rw [hF, ModularForm.coe_zero, qC_zero] at hxe
    rcases mul_eq_zero.mp hxe with e | e
    · exact hιx e
    · exact hG ((qC_eq_zero_iff G).mp e)
  refine ⟨inv_mem hxm, k, G, F, hF, ?_, ?_, ?_⟩
  · rw [map_inv₀, ← hxe, inv_mul_cancel_left₀ hιx]
  · intro ρ hρ
    exact ⟨(hxE ρ hρ).2, (hxE ρ hρ).1⟩
  · intro hx' ρ hρ τ hτ
    have e : (⟨x⁻¹, hx'⟩ : KL L m M') = (⟨x, hxm⟩ : KL L m M')⁻¹ := Subtype.ext rfl
    have h1 := hxτ hxm ρ hρ τ hτ
    have hFq : qC (sl hmM' ρ hρ F) ≠ 0 := fun e => sl_ne_zero hmM' ρ hρ hF ((qC_eq_zero_iff _).mp e)
    have hτx : ιB ι₀ ((τ ⟨x, hxm⟩ : KL L m M') : LaurentSeries L) ≠ 0 := by
      intro e0; rw [e0, zero_mul] at h1; exact hFq h1.symm
    rw [e, map_inv₀, IntermediateField.coe_inv, map_inv₀, ← h1, inv_mul_cancel_left₀ hτx]

theorem rat_coeff_mul {k : ℤ} (f g : ModularForm (Γ m M') k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(f.mul g))).coeff n = (r : ℂ) := by
  rw [ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g, ← hf, ← hg,
    ← map_mul, PowerSeries.coeff_map]
  exact ⟨((PowerSeries.coeff n (pf * pg) : ℤ) : ℚ), by simp⟩

theorem Good.gen (hι₀ : ι₀ ξ = em m) {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH m M')) :
    Good hmM' ξ ι₀ (coeffEmb L y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  have hmem : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ KL L m M' :=
    coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hg0)
  have hgq : qC (⇑g) ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0
  have hgne : g ≠ 0 := fun e => hgq ((qC_eq_zero_iff g).mpr e)
  have hk : Even (k + k) := ⟨k, rfl⟩
  refine ⟨hmem, k + k, f.mul g, g.mul g, mul_ne_zero_form hgne hgne, ?_, ?_, ?_⟩
  · rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, ModularForm.coe_mul, ModularForm.coe_mul,
      qC_mul, qC_mul]
    field_simp
  · intro ρ hρ
    exact ⟨inE_sl_of_rat ι₀ hmM' hι₀ hk (f.mul g) (rat_coeff_mul f g hf hg) ρ hρ,
      inE_sl_of_rat ι₀ hmM' hι₀ hk (g.mul g) (rat_coeff_mul g g hg hg) ρ hρ⟩
  · intro hx ρ hρ τ hτ

    have key := hτ k f g pf pg hf hg hg0 ⟨_, hx⟩ rfl ι₀ hι₀
    change ιB ι₀ ((τ ⟨_, hx⟩ : KL L m M') : LaurentSeries L) * qC (sl hmM' ρ hρ g) = qC (sl hmM' ρ hρ f) at key
    rw [sl_mul_coe, sl_mul_coe, qC_mul, qC_mul, ← key]
    ring

theorem Good.of_mem_field (hι₀ : ι₀ ξ = em m) {y : LaurentSeries ℚ}
    (hy : y ∈ xHFunctionField (m ^ 2 * M') (levelH m M')) : Good hmM' ξ ι₀ (coeffEmb L y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M')) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact Good.const _
      · exact Good.gen hι₀ hy
  | one => rw [map_one, ← map_one (algebraMap L (LaurentSeries L))]; exact Good.const _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem Good.of_mem (hι₀ : ι₀ ξ = em m) {x : LaurentSeries L} (hx : x ∈ KL L m M') : Good hmM' ξ ι₀ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact Good.const c
      · exact Good.of_mem_field hι₀ hz
  | one => rw [← map_one (algebraMap L (LaurentSeries L))]; exact Good.const _
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Good
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Norm

variable {n m : ℕ} [NeZero n] [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M') (hnm : n ∣ m)
variable {L : Type} [Field L] [CharZero L] {ξ : L} (ι₀ : L →+* ℂ)

theorem sl_one_eq {k : ℤ} (F : ModularForm (Γ m M') k) : sl hmM' 1 (one_mem _) F = F := by
  ext τ
  simp only [coe_sl, ← shp_apply, map_one, SlashAction.slash_one]

theorem qC_prod_mem {ι : Type} (s : Finset ι) {k : ℤ} (F : ι → ModularForm (Γ m M') k)
    (hF : ∀ i ∈ s, InE ι₀ (F i)) : qC (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) ∈ Efield ι₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, qC_one]; exact one_mem _
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, ← ModularForm.coe_prodEqualWeights (s := t) F, qC_mul]
      rw [ModularForm.coe_prodEqualWeights]
      exact mul_mem (hF a (Finset.mem_insert_self a t)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

include hmM' hnm

theorem norm_step (w : KL L m M') (hgood : Good hmM' ξ ι₀ (w : LaurentSeries L))
    (hexτ : ∀ ρ ∈ Δ n M', ∃ τ : KL L m M' ≃ₐ[L] KL L m M',
      IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') ρ (KL L m M') τ ∧ τ w = w) :
    ∃ (k' : ℤ) (Φ Ψ : ModularForm (Hgp n m M') k'), (⇑Ψ : ℍ → ℂ) ≠ 0 ∧ qC Φ ∈ Efield ι₀ ∧ qC Ψ ∈ Efield ι₀ ∧
      ιB ι₀ (w : LaurentSeries L) * qC Ψ = qC Φ := by
  haveI := isFiniteRelIndex_Γ_Hgp (n := n) hmM' hnm (M' := M')
  obtain ⟨_, k, F, G, hG, hwe, hE, hτ⟩ := hgood
  have hGq : qC (⇑G) ≠ 0 := fun e => hG ((qC_eq_zero_iff G).mp e)

  have hFG : ∀ h ∈ Hgp n m M', ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h) := by
    intro h hh
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Hgp_iff h).mp hh
    have hρ0 : ρ ∈ Gamma0 M' := (mem_Δ_iff.mp hρ).2
    obtain ⟨τ, hτ', hτfix⟩ := hexτ ρ hρ
    have h1 := hτ w.2 ρ hρ0 τ hτ'
    rw [Subtype.coe_eta, hτfix] at h1

    have h2 : qC (sl hmM' ρ hρ0 F) * qC G = qC F * qC (sl hmM' ρ hρ0 G) := by
      rw [← h1, ← hwe]; ring
    have h3 := mul_eq_mul_of_qC (sl hmM' ρ hρ0 F) G F (sl hmM' ρ hρ0 G) rfl h2
    simpa only [coe_sl] using h3
  obtain ⟨Φ, hΦ⟩ := ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq (Γ m M') (Hgp n m M') F G hFG
  set Ψ := ModularForm.norm (Hgp n m M') G with hΨdef
  have hGne : (⇑G : ℍ → ℂ) ≠ 0 := fun e => hG (DFunLike.ext' (by rw [e, ModularForm.coe_zero]))
  have hΨne : (⇑Ψ : ℍ → ℂ) ≠ 0 := by
    intro e
    exact ModularForm.norm_ne_zero (Hgp n m M') hGne (DFunLike.ext' (by rw [← hΨdef, e, ModularForm.coe_zero]))

  have hΨE : qC (⇑Ψ) ∈ Efield ι₀ := by
    letI := Fintype.ofFinite (Hgp n m M' ⧸ (Γ m M').subgroupOf (Hgp n m M'))
    have hρc : ∀ c : Hgp n m M' ⧸ (Γ m M').subgroupOf (Hgp n m M'), ∃ ρ : SL(2, ℤ), ∃ hρ : ρ ∈ Gamma0 M',
        SlashInvariantForm.quotientFunc G c = ⇑(sl hmM' ρ hρ G) := by
      intro c
      have hinv : ((c.out : Hgp n m M') : GL (Fin 2) ℝ)⁻¹ ∈ Hgp n m M' := inv_mem c.out.2
      obtain ⟨ρ, hρ, e⟩ := (mem_Hgp_iff _).mp hinv
      refine ⟨ρ, (mem_Δ_iff.mp hρ).2, ?_⟩
      conv_lhs => rw [← Quotient.out_eq c]
      rw [SlashInvariantForm.quotientFunc_mk, coe_sl, e]
    choose ρ hρ hρe using hρc
    rw [hΨdef, ModularForm.coe_norm]
    have : (∏ c, SlashInvariantForm.quotientFunc G c : ℍ → ℂ) = ∏ c ∈ Finset.univ, (⇑(sl hmM' (ρ c) (hρ c) G) : ℍ → ℂ) :=
      Finset.prod_congr rfl fun c _ => hρe c
    rw [this]
    exact qC_prod_mem ι₀ _ _ fun c _ => (hE (ρ c) (hρ c)).2

  set Φr : ModularForm (Γ m M') _ := restrictForm (Γ_le_Hgp hmM' hnm) Φ
  set Ψr : ModularForm (Γ m M') _ := restrictForm (Γ_le_Hgp hmM' hnm) Ψ
  have hq : qC (⇑Φ) * qC G = qC F * qC (⇑Ψ) := by
    rw [show (⇑Φ : ℍ → ℂ) = ⇑Φr from rfl, show (⇑Ψ : ℍ → ℂ) = ⇑Ψr from rfl, ← qC_mul, ← qC_mul]
    exact congrArg qC hΦ
  have hFE : qC (⇑F) ∈ Efield ι₀ := by simpa only [InE, sl_one_eq] using (hE 1 (one_mem _)).1
  have hGE : qC (⇑G) ∈ Efield ι₀ := by simpa only [InE, sl_one_eq] using (hE 1 (one_mem _)).2
  refine ⟨_, Φ, Ψ, hΨne, ?_, hΨE, ?_⟩
  · have : qC (⇑Φ) = qC F * qC (⇑Ψ) / qC G := by rw [← hq, mul_div_cancel_right₀ _ hGq]
    rw [this]
    exact div_mem (mul_mem hFE hΨE) hGE
  · apply mul_right_cancel₀ hGq
    rw [mul_assoc, mul_comm (qC (⇑Ψ)), ← mul_assoc, hwe, hq]

end Norm
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

section Unstretch

variable {q ℓ : ℕ} [NeZero q] [NeZero ℓ] {M' : ℕ} [NeZero M']
variable {L : Type} [Field L] [CharZero L] (ι₀ : L →+* ℂ)

scoped instance : NeZero (q * ℓ) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne ℓ)⟩

theorem Dr_mul_Dr : Dr (q * ℓ) = Dr q * Dr ℓ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem le_unstretch : Γ q M' ≤ ConjAct.toConjAct ((Dr ℓ)⁻¹)⁻¹ • Hgp q (q * ℓ) M' := by
  intro A hA
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul,
    inv_inv, mem_Hgp_iff]
  obtain ⟨A', hA', rfl⟩ := hA
  refine ⟨upSL A' (m_dvd_lowerLeft_of_mem_GH hA'), upSL_mem_Δ hA', ?_⟩
  have hup := upSL_coe A' (m_dvd_lowerLeft_of_mem_GH hA')
  have e : ((upSL A' (m_dvd_lowerLeft_of_mem_GH hA') : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      Dr q * (A' : GL (Fin 2) ℝ) * (Dr q)⁻¹ := by
    rw [← hup, mul_inv_cancel_right]
  rw [conjElemN_eq, e, Dr_mul_Dr]
  change _ = (Dr ℓ)⁻¹ * (A' : GL (Fin 2) ℝ) * Dr ℓ
  group

def unstretch {k : ℤ} (Φ : ModularForm (Hgp q (q * ℓ) M') k) : ModularForm (Γ q M') k :=
  restrictForm le_unstretch (ModularForm.translate Φ (Dr ℓ)⁻¹)

theorem coe_unstretch {k : ℤ} (Φ : ModularForm (Hgp q (q * ℓ) M') k) :
    (⇑(unstretch Φ) : ℍ → ℂ) = (⇑Φ : ℍ → ℂ) ∣[k] (Dr ℓ)⁻¹ := rfl

theorem unstretch_slash {k : ℤ} (Φ : ModularForm (Hgp q (q * ℓ) M') k) :
    (⇑(unstretch Φ) : ℍ → ℂ) ∣[k] Dr ℓ = ⇑Φ := by
  rw [coe_unstretch, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem unstretch_coe_ne_zero {k : ℤ} {Φ : ModularForm (Hgp q (q * ℓ) M') k} (h : (⇑Φ : ℍ → ℂ) ≠ 0) :
    unstretch Φ ≠ 0 := by
  intro e
  apply h
  rw [← unstretch_slash Φ, e, ModularForm.coe_zero, SlashAction.zero_slash]

theorem qC_stretch (hqlM' : Nat.Coprime (q * ℓ) M') {k : ℤ} (Φ : ModularForm (Hgp q (q * ℓ) M') k) :
    qC (⇑Φ) = HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) * qExpand ℂ ℓ (qC (unstretch Φ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓC : ((ℓ : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ)
  set Φ₁ := unstretch Φ with hΦ₁

  set Φr : ModularForm (Γ (q * ℓ) M') k := restrictForm (Γ_le_Hgp hqlM' (dvd_mul_right q ℓ)) Φ with hΦr

  have hfun : (fun τ : ℍ => Φ₁ (Dr ℓ • τ)) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • (⇑Φr : ℍ → ℂ) := by
    funext τ
    have := congrFun (unstretch_slash Φ) τ
    rw [ModularForm.slash_heckeDiagMatrix_apply k hℓ] at this
    rw [Pi.smul_apply, smul_eq_mul, show (⇑Φr : ℍ → ℂ) τ = Φ τ from rfl, ← this, ← mul_assoc,
      inv_mul_cancel₀ hℓC, one_mul]
  have hper : Function.Periodic ((⇑Φ₁ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex Φ₁ one_mem_strictPeriods
  have hcoef : ∀ nn : ℕ, ((ℓ : ℂ) ^ (k - 1))⁻¹ * (qExpansion 1 (⇑Φr)).coeff nn =
      if ℓ ∣ nn then (qExpansion 1 (⇑Φ₁)).coeff (nn / ℓ) else 0 := by
    intro nn
    have h := UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hper Φ₁.holo' (ModularFormClass.bdd_at_infty Φ₁) hℓ nn
    simp only [ModularFormClass.qCoeff] at h
    rw [hfun, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ Φr, map_smul, smul_eq_mul] at h
    exact h

  rw [show (⇑Φ : ℍ → ℂ) = ⇑Φr from rfl, HahnSeries.C_mul_eq_smul]
  ext j
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  by_cases hdvd : (ℓ : ℤ) ∣ j
  · obtain ⟨j', rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    rcases lt_or_ge j' 0 with hj | hj
    · rw [qC_coeff_neg _ hj, qC_coeff_neg _ (mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hℓ) hj),
        mul_zero]
    · obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [show ((ℓ : ℤ) * (nn : ℤ)) = ((ℓ * nn : ℕ) : ℤ) by push_cast; ring, qC_coeff_nat, qC_coeff_nat]
      have h := hcoef (ℓ * nn)
      rw [if_pos (dvd_mul_right ℓ nn), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)] at h
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hℓC, one_mul]
  · rw [qExpand_coeff_of_not_dvd _ _ hdvd, mul_zero]
    rcases lt_or_ge j 0 with hj | hj
    · exact qC_coeff_neg _ hj
    · obtain ⟨nn, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [qC_coeff_nat]
      have h := hcoef nn
      have hnd : ¬ ℓ ∣ nn := fun hd => hdvd (Int.natCast_dvd_natCast.mpr hd)
      rw [if_neg hnd] at h
      rcases mul_eq_zero.mp h with e | e
      · exact absurd e (inv_ne_zero hℓC)
      · exact e

theorem mem_Efield_of_qExpand {y : LaurentSeries ℂ} (h : qExpand ℂ ℓ y ∈ Efield ι₀) : y ∈ Efield ι₀ := by
  rw [mem_Efield_iff] at h ⊢
  intro j
  rw [← qExpand_coeff_mul ℓ y j]
  exact h _

theorem ιB_qExpand (x : LaurentSeries L) : ιB ι₀ (qExpand L ℓ x) = qExpand ℂ ℓ (ιB ι₀ x) := by
  ext j
  rw [coeffMap_coeff]
  by_cases hdvd : (ℓ : ℤ) ∣ j
  · obtain ⟨j', rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ hdvd, qExpand_coeff_of_not_dvd _ _ hdvd, map_zero]

theorem descent_step (hqlM' : Nat.Coprime (q * ℓ) M') {k' : ℤ} (Φ Ψ : ModularForm (Hgp q (q * ℓ) M') k')
    (hΨ : (⇑Ψ : ℍ → ℂ) ≠ 0) (hΦE : qC (⇑Φ) ∈ Efield ι₀) (hΨE : qC (⇑Ψ) ∈ Efield ι₀) :
    ∃ x : LaurentSeries L, x ∈ laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M')) ∧
      ιB ι₀ (qExpand L ℓ x) * qC (⇑Ψ) = qC (⇑Φ) := by
  have hℓC : ((ℓ : ℂ) ^ (k' - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))
  have hCmem : (HahnSeries.C ((ℓ : ℂ) ^ (k' - 1)) : LaurentSeries ℂ) ∈ Efield ι₀ := by
    have : ((ℓ : ℂ) ^ (k' - 1)) = ι₀ ((ℓ : L) ^ (k' - 1)) := by rw [map_zpow₀, map_natCast]
    rw [this]; exact C_mem_Efield ι₀ _
  have hCne : (HahnSeries.C ((ℓ : ℂ) ^ (k' - 1)) : LaurentSeries ℂ) ≠ 0 := fun h =>
    hℓC (HahnSeries.C_injective (by rw [h, map_zero]))

  have hE1 : ∀ (Θ : ModularForm (Hgp q (q * ℓ) M') k'), qC (⇑Θ) ∈ Efield ι₀ → InE ι₀ (unstretch Θ) := by
    intro Θ hΘ
    refine mem_Efield_of_qExpand (ℓ := ℓ) ι₀ ?_
    have : qExpand ℂ ℓ (qC (⇑(unstretch Θ))) = (HahnSeries.C ((ℓ : ℂ) ^ (k' - 1)))⁻¹ * qC (⇑Θ) := by
      rw [qC_stretch hqlM' Θ, inv_mul_cancel_left₀ hCne]
    rw [this]
    exact mul_mem (inv_mem hCmem) hΘ
  have hΦ₁ := (inE_iff ι₀ _).mp (hE1 Φ hΦE)
  have hΨ₁ := (inE_iff ι₀ _).mp (hE1 Ψ hΨE)
  obtain ⟨x, hx, hxe⟩ :=
    ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range (q ^ 2 * M')
      (levelH q M') (unstretch Φ) (unstretch Ψ) (unstretch_coe_ne_zero hΨ) L ι₀ hΦ₁ hΨ₁
  refine ⟨x, hx, ?_⟩
  change ιB ι₀ x * qC (⇑(unstretch Ψ)) = qC (⇑(unstretch Φ)) at hxe
  have h := congrArg (fun z => HahnSeries.C ((ℓ : ℂ) ^ (k' - 1)) * qExpand ℂ ℓ z) hxe
  simp only [map_mul] at h
  rw [ιB_qExpand (ℓ := ℓ), qC_stretch hqlM' Ψ, qC_stretch hqlM' Φ, ← h]
  ring

end Unstretch
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA"

end R4GC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

section FAG

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)

include hι₀ in

theorem isImgC_of_isLevelAutAt (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (σ : KL L m M' ≃ₐ[L] KL L m M')
    (hσ : IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') γ (KL L m M') σ) (X : KL L m M') :
    IsImgC hmM' γ hγ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ (σ X : LaurentSeries L)) := by

  suffices key : ∀ (x : LaurentSeries L), x ∈ KL L m M' → ∀ hx : x ∈ KL L m M',
      IsImgC hmM' γ hγ (ιB ι₀ x) (ιB ι₀ (σ ⟨x, hx⟩ : LaurentSeries L)) from key X X.2 X.2
  intro x hx
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    intro hx
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    · have e : σ ⟨algebraMap L (LaurentSeries L) c, hx⟩ = algebraMap L (KL L m M') c :=
        (congrArg σ (Subtype.ext rfl)).trans (σ.commutes c)
      rw [e]
      show IsImgC hmM' γ hγ (ιB ι₀ (algebraMap L (LaurentSeries L) c)) (ιB ι₀ (algebraMap L (LaurentSeries L) c))
      rw [← C_eq_algebraMap, ιB_C]
      exact IsImgC.const _
    ·
      revert hx
      change z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M')) at hz
      induction hz using Subfield.closure_induction with
      | mem y hy =>
        intro hx
        rcases hy with ⟨r, rfl⟩ | hy
        · have e0 : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (r : L) := by
            rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
            simp
          have e : σ ⟨coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r), hx⟩ = algebraMap L (KL L m M') (r : L) :=
            (congrArg σ (Subtype.ext e0)).trans (σ.commutes (r : L))
          rw [e, e0]
          show IsImgC hmM' γ hγ (ιB ι₀ (algebraMap L (LaurentSeries L) (r : L))) (ιB ι₀ (algebraMap L (LaurentSeries L) (r : L)))
          rw [← C_eq_algebraMap, ιB_C]
          exact IsImgC.const _
        · obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
          refine ⟨k, f, g, ne_zero_of_intSeriesC_ne_zero hg hg0, ?_, ?_⟩
          · rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
          · exact hσ k f g pf pg hf hg hg0 ⟨_, hx⟩ rfl ι₀ hι₀
      | one =>
        intro hx
        have e : σ ⟨coeffEmb L 1, hx⟩ = 1 := by
          have h1 : (⟨coeffEmb L 1, hx⟩ : KL L m M') = 1 := Subtype.ext (map_one _)
          rw [h1, map_one]
        rw [e]
        simp only [map_one, OneMemClass.coe_one]
        exact IsImgC.one
      | add a b ha hb iha ihb =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L ha
        have hb' : coeffEmb L b ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L hb
        have e : σ ⟨coeffEmb L (a + b), hx⟩ = σ ⟨_, ha'⟩ + σ ⟨_, hb'⟩ := by
          rw [← map_add]; exact congrArg σ (Subtype.ext (map_add _ _ _))
        rw [e, map_add, map_add, AddMemClass.coe_add, map_add]
        exact (iha ha').add (ihb hb')
      | neg a ha iha =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L ha
        have e : σ ⟨coeffEmb L (-a), hx⟩ = -σ ⟨_, ha'⟩ := by
          rw [← map_neg]; exact congrArg σ (Subtype.ext (map_neg _ _))
        rw [e, map_neg, map_neg, NegMemClass.coe_neg, map_neg]
        exact (iha ha').neg
      | inv a ha iha =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L ha
        have e : σ ⟨coeffEmb L a⁻¹, hx⟩ = (σ ⟨_, ha'⟩)⁻¹ := by
          rw [← map_inv₀]; exact congrArg σ (Subtype.ext (map_inv₀ _ _))
        rw [e]
        have h' := (iha ha').inv
        simp only [map_inv₀, IntermediateField.coe_inv] at h' ⊢
        exact h'
      | mul a b ha hb iha ihb =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L ha
        have hb' : coeffEmb L b ∈ KL L m M' := coeffEmb_mem_laurentBaseChange L hb
        have e : σ ⟨coeffEmb L (a * b), hx⟩ = σ ⟨_, ha'⟩ * σ ⟨_, hb'⟩ := by
          rw [← map_mul]; exact congrArg σ (Subtype.ext (map_mul _ _ _))
        rw [e, map_mul, map_mul, MulMemClass.coe_mul, map_mul]
        exact (iha ha').mul (ihb hb')
  | one =>
    intro hx
    have e : σ ⟨1, hx⟩ = 1 := by
      have h1 : (⟨1, hx⟩ : KL L m M') = 1 := Subtype.ext rfl
      rw [h1, map_one]
    rw [e]
    simp only [map_one, OneMemClass.coe_one]
    exact IsImgC.one
  | add a b ha hb iha ihb =>
    intro hx
    have ha' : a ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact ha
    have hb' : b ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact hb
    have e : σ ⟨a + b, hx⟩ = σ ⟨a, ha'⟩ + σ ⟨b, hb'⟩ := by rw [← map_add]; rfl
    rw [e, map_add, AddMemClass.coe_add, map_add]
    exact (iha ha').add (ihb hb')
  | neg a ha iha =>
    intro hx
    have ha' : a ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact ha
    have e : σ ⟨-a, hx⟩ = -σ ⟨a, ha'⟩ := by rw [← map_neg]; rfl
    rw [e, map_neg, NegMemClass.coe_neg, map_neg]
    exact (iha ha').neg
  | inv a ha iha =>
    intro hx
    have ha' : a ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact ha
    have e : σ ⟨a⁻¹, hx⟩ = (σ ⟨a, ha'⟩)⁻¹ := by rw [← map_inv₀]; rfl
    rw [e]
    have h' := (iha ha').inv
    simp only [map_inv₀, IntermediateField.coe_inv] at h' ⊢
    exact h'
  | mul a b ha hb iha ihb =>
    intro hx
    have ha' : a ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact ha
    have hb' : b ∈ KL L m M' := by rw [mem_laurentBaseChange_iff]; exact hb
    have e : σ ⟨a * b, hx⟩ = σ ⟨a, ha'⟩ * σ ⟨b, hb'⟩ := by rw [← map_mul]; rfl
    rw [e, map_mul, MulMemClass.coe_mul, map_mul]
    exact (iha ha').mul (ihb hb')

include hι₀ in

theorem eq_τEquiv_of_isLevelAutAt (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (σ : KL L m M' ≃ₐ[L] KL L m M')
    (hσ : IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') γ (KL L m M') σ) :
    σ = τEquiv hmM' ξ ι₀ hι₀ γ hγ := by
  refine AlgEquiv.ext fun X => Subtype.ext ?_
  rw [τEquiv_apply]
  exact (Φfun_eq hmM' ξ ι₀ hι₀ γ hγ (isImgC_of_isLevelAutAt hmM' ξ ι₀ hι₀ γ hγ σ hσ X)).symm

include hι₀ in

theorem τEquiv_mul (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M') :
    τEquiv hmM' ξ ι₀ hι₀ (δ * γ) (mul_mem hδ hγ) = τEquiv hmM' ξ ι₀ hι₀ γ hγ * τEquiv hmM' ξ ι₀ hι₀ δ hδ := by
  refine AlgEquiv.ext fun X => Subtype.ext ?_
  rw [τEquiv_apply, AlgEquiv.mul_apply]
  refine Φfun_eq hmM' ξ ι₀ hι₀ (δ * γ) (mul_mem hδ hγ) ?_

  set Y := τEquiv hmM' ξ ι₀ hι₀ δ hδ X with hY
  have h1 : IsImgC hmM' δ hδ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ (Y : LaurentSeries L)) := by
    rw [hY, τEquiv_apply]; exact isImgC_Φfun hmM' ξ ι₀ hι₀ δ hδ X
  have h2 : IsImgC hmM' γ hγ (ιB ι₀ (Y : LaurentSeries L)) (ιB ι₀ (τEquiv hmM' ξ ι₀ hι₀ γ hγ Y : LaurentSeries L)) := by
    rw [τEquiv_apply]; exact isImgC_Φfun hmM' ξ ι₀ hι₀ γ hγ Y
  obtain ⟨k, f, g, hg, hXr, hYr⟩ := h1
  have hslg : sl hmM' δ hδ g ≠ 0 := sl_ne_zero hmM' δ hδ hg
  have hYrep : ιB ι₀ (Y : LaurentSeries L) = qC (sl hmM' δ hδ f) / qC (sl hmM' δ hδ g) := by
    rw [eq_div_iff (qC_sl_ne_zero hmM' δ hδ hg)]; exact hYr
  have h3 := h2.apply_rep (sl hmM' δ hδ f) (sl hmM' δ hδ g) hslg hYrep
  rw [sl_sl, sl_sl] at h3
  exact ⟨k, f, g, hg, hXr, h3⟩

end FAG
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

section FAGK

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)

include hι₀ in

theorem τEquiv_eq_one_of_mem_Δ (ε : SL(2, ℤ)) (hε : ε ∈ R4GC.Δ m M') :
    τEquiv hmM' ξ ι₀ hι₀ ε (R4GC.mem_Δ_iff.mp hε).2 = 1 := by
  have hε0 : ε ∈ Gamma0 M' := (R4GC.mem_Δ_iff.mp hε).2
  have hmemΓ : conjElemN m ε ∈ Γ m M' := (R4GC.mem_Γ_iff_exists hmM' _).mpr ⟨ε, hε, rfl⟩
  have hsl : ∀ {k : ℤ} (f : ModularForm (Γ m M') k), qC (⇑(sl hmM' ε hε0 f)) = qC (⇑f) := by
    intro k f
    rw [coe_sl, SlashInvariantFormClass.slash_action_eq f (conjElemN m ε) hmemΓ]
  refine AlgEquiv.ext fun X => Subtype.ext ?_
  rw [τEquiv_apply, AlgEquiv.one_apply]
  refine Φfun_eq hmM' ξ ι₀ hι₀ ε hε0 ?_
  obtain ⟨k, f, g, hg, hXr, -⟩ := isImgC_Φfun hmM' ξ ι₀ hι₀ ε hε0 X
  refine ⟨k, f, g, hg, hXr, ?_⟩
  rw [hsl, hsl, hXr, div_mul_cancel₀ _ (fun e => hg ((qC_eq_zero_iff g).mp e))]

end FAGK
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

namespace R4GC
section TF
variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M']
theorem qC_add' {k : ℤ} (f g : ModularForm (Γ m M') k) : qC (⇑(f + g)) = qC (⇑f) + qC (⇑g) := by
  rw [ModularForm.coe_add, qC_add]
theorem qC_smul' {k : ℤ} (c : ℂ) (f : ModularForm (Γ m M') k) : qC (⇑(c • f)) = HahnSeries.C c * qC (⇑f) := by
  rw [ModularForm.IsGLPos.coe_smul, qC_smul]
end TF
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"
end R4GC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.W1xLA P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.R4GC"

set_option maxHeartbeats 16000000 in
open R4GC in
theorem cuspForms_levelH
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Fact.out : q.Prime).ne_zero).unit
    ∃ (Aw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 3)
      (C4 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C6 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 6),
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.cuspPoint L q ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Aw v))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₄ ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₆ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C4 ∧
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C6 ∧
        ∀ v : Fin 2 → ZMod q,
          (⇑(Aw v) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Aw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Bw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by
  haveI hN : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hN1 : 1 < q := (Fact.out : q.Prime).one_lt
  haveI : Fact (1 < q) := ⟨hN1⟩
  obtain ⟨Rw, hRq, hRs⟩ := ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint q M' hqM' L ξ hξ ι hι
  obtain ⟨Sw, C4, hSq, hC4q, hS4⟩ := ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour q M' hqM' L ξ hξ ι hι
  obtain ⟨C6, hC6q, hC6s⟩ := ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase q M' hqM' L ι
  set ξu : Lˣ := (hξ.isUnit (Fact.out : q.Prime).ne_zero).unit with hξu

  have hw : (3 : ℤ) + 3 = 6 := by norm_num
  let Aw : (Fin 2 → ZMod q) → ModularForm (R4GC.Γ q M') 6 := fun v =>
    ModularForm.mcast hw ((Rw v).mul (Rw v)) + ((216 : ℂ)⁻¹) • C6
  let Bw : (Fin 2 → ZMod q) → ModularForm (R4GC.Γ q M') 4 := fun v =>
    (4 : ℂ) • Sw v + (-(12 : ℂ)⁻¹) • C4
  have hAq : ∀ v, R4GC.qC (⇑(Aw v)) = R4GC.qC (⇑(Rw v)) ^ 2 + HahnSeries.C ((216 : ℂ)⁻¹) * R4GC.qC (⇑C6) := by
    intro v
    dsimp only [Aw]
    rw [R4GC.qC_add', R4GC.qC_smul', ModularForm.coe_mcast, ModularForm.coe_mul, R4GC.qC_mul, sq]
  have hBq : ∀ v, R4GC.qC (⇑(Bw v)) = HahnSeries.C (4 : ℂ) * R4GC.qC (⇑(Sw v)) + HahnSeries.C (-(12 : ℂ)⁻¹) * R4GC.qC (⇑C4) := by
    intro v
    dsimp only [Bw]
    rw [R4GC.qC_add', R4GC.qC_smul', R4GC.qC_smul']
  refine ⟨Aw, Bw, Rw, C4, C6, ?_, hC4q, hC6q, ?_⟩
  · intro v hv0
    obtain ⟨hSv⟩ := (⟨(hSq v hv0)⟩ : PLift _)
    have hRv := hRq v hv0

    have hSv' : R4GC.qC (⇑(Sw v)) = R4GC.ιB ι (((ModularCurve.cuspPoint L q ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2) := hSv
    have hRv' : R4GC.qC (⇑(Rw v)) = R4GC.ιB ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1) := hRv
    have hC4' : R4GC.qC (⇑C4) = R4GC.ιB ι (ModularCurve.tateBase L q).c₄ := hC4q
    have hC6' : R4GC.qC (⇑C6) = R4GC.ιB ι (ModularCurve.tateBase L q).c₆ := hC6q
    have hιC : ∀ a : L, R4GC.ιB ι (HahnSeries.C a) = HahnSeries.C (ι a) := fun a => by
      rw [HahnSeries.C_apply, R4GC.ιB, coeffMap_single, HahnSeries.C_apply]
    set x := (ModularCurve.cuspPoint L q ξu v).1 with hxdef
    set y := (ModularCurve.cuspPoint L q ξu v).2 with hydef

    have hBι : R4GC.qC (⇑(Bw v)) =
        R4GC.ιB ι (HahnSeries.C (4 : L) * (x + HahnSeries.C ((12 : L)⁻¹)) ^ 2 +
          HahnSeries.C (-(12 : L)⁻¹) * (ModularCurve.tateBase L q).c₄) := by
      rw [hBq v, hSv', hC4']
      simp only [map_add, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
    have hAι : R4GC.qC (⇑(Aw v)) =
        R4GC.ιB ι ((2 * y + x) ^ 2 + HahnSeries.C ((216 : L)⁻¹) * (ModularCurve.tateBase L q).c₆) := by
      rw [hAq v, hRv', hC6']
      simp only [map_add, map_mul, map_pow, map_neg, map_inv₀, map_ofNat, hιC]

    have ha1 : (ModularCurve.tateBase L q).a₁ = 1 := by simp [ModularCurve.tateBase, ModularCurve.tateLaurent]
    have ha2 : (ModularCurve.tateBase L q).a₂ = 0 := by simp [ModularCurve.tateBase, ModularCurve.tateLaurent]
    have ha3 : (ModularCurve.tateBase L q).a₃ = 0 := by simp [ModularCurve.tateBase, ModularCurve.tateLaurent]
    have ha4 : (ModularCurve.tateBase L q).a₄ = ModularCurve.qExpand L q (ModularCurve.laurentOfInt L ModularCurve.tateA4) := by
      simp [ModularCurve.tateBase]
    have ha6 : (ModularCurve.tateBase L q).a₆ = ModularCurve.qExpand L q (ModularCurve.laurentOfInt L ModularCurve.tateA6) := by
      simp [ModularCurve.tateBase]
    have hon : (ModularCurve.tateBase L q).toAffine.Equation x y := by
      by_cases hv1 : v 1 = 0
      · have hv0' : v 0 ≠ 0 := by
          intro h0; apply hv0; funext i; fin_cases i <;> simp [h0, hv1]
        rw [hxdef, hydef, ModularCurve.cuspPoint_of_eq_zero _ hv1]
        apply ModularCurve.equation_tateBase_tateToricPoint
        rw [isUnit_iff_ne_zero, sub_ne_zero, ne_comm, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
        intro h1
        have hd := (hξ.pow_eq_one_iff_dvd _).mp h1
        have hlt : (v 0).val < q := ZMod.val_lt _
        have hpos : 0 < (v 0).val := by
          rw [Nat.pos_iff_ne_zero]; exact fun e => hv0' ((ZMod.val_eq_zero _).mp e)
        exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr hlt)
      · rw [hxdef, hydef, ModularCurve.cuspPoint_of_ne_zero _ hv1]
        apply ModularCurve.equation_tateBase_nonToricPoint
        · rw [Nat.pos_iff_ne_zero]; exact fun e => hv1 ((ZMod.val_eq_zero _).mp e)
        · exact ZMod.val_lt _
    have heq : y ^ 2 + x * y = x ^ 3 + (ModularCurve.tateBase L q).a₄ * x + (ModularCurve.tateBase L q).a₆ := by
      rw [ha4, ha6]; exact (ModularCurve.equation_tateBase_iff L q x y).mp hon

    have hc4def : (ModularCurve.tateBase L q).c₄ = 1 - 48 * (ModularCurve.tateBase L q).a₄ := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha1, ha2, ha3]; ring
    have hc6def : (ModularCurve.tateBase L q).c₆ =
        -1 + 72 * (ModularCurve.tateBase L q).a₄ - 864 * (ModularCurve.tateBase L q).a₆ := by
      simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, ha1, ha2, ha3]; ring
    have h4 : (HahnSeries.C (4 : L) : LaurentSeries L) = 4 := map_ofNat _ 4
    have hneg : (HahnSeries.C (-(12 : L)⁻¹) : LaurentSeries L) = -HahnSeries.C ((12 : L)⁻¹) := map_neg _ _
    have hu : 12 * (HahnSeries.C ((12 : L)⁻¹) : LaurentSeries L) = 1 := by
      rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := L)) 12, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
    have hw : (HahnSeries.C ((216 : L)⁻¹) : LaurentSeries L) = 8 * HahnSeries.C ((12 : L)⁻¹) ^ 3 := by
      rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := L)) 8, ← map_pow, ← map_mul]; congr 1; norm_num
    have hid : (x + HahnSeries.C ((12 : L)⁻¹)) *
        (HahnSeries.C (4 : L) * (x + HahnSeries.C ((12 : L)⁻¹)) ^ 2 + HahnSeries.C (-(12 : L)⁻¹) * (ModularCurve.tateBase L q).c₄) =
        (2 * y + x) ^ 2 + HahnSeries.C ((216 : L)⁻¹) * (ModularCurve.tateBase L q).c₆ := by
      rw [h4, hneg, hc4def, hc6def]
      set u : LaurentSeries L := HahnSeries.C ((12 : L)⁻¹) with hudef
      set w : LaurentSeries L := HahnSeries.C ((216 : L)⁻¹) with hwdef
      set a₄ := (ModularCurve.tateBase L q).a₄
      set a₆ := (ModularCurve.tateBase L q).a₆
      linear_combination (-4) * heq +
        (x ^ 2 + x * u + 4 * a₄ * x + u ^ 2 - 48 * a₄ * u ^ 2 + 4 * a₆ * (144 * u ^ 2 + 12 * u + 1)) * hu +
        (1 - 72 * a₄ + 864 * a₆) * hw
    refine ⟨?_, ⟨_, hBι⟩, ?_, hRv⟩
    ·
      show R4GC.qC (⇑(Bw v)) ≠ 0
      rw [hBι]
      intro h0
      have hb0 := R4GC.ιB_injective ι (h0.trans (map_zero _).symm)

      have hC0 : ∀ a : L, (HahnSeries.C a : LaurentSeries L).coeff 0 = a := fun a => by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
      have hCmul : ∀ (a : L) (z : LaurentSeries L), (HahnSeries.C a * z).coeff 0 = a * z.coeff 0 := fun a z => by
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
      have ha40 : (ModularCurve.tateBase L q).a₄.coeff 0 = 0 := by
        rw [ha4, show (0 : ℤ) = ((q : ℕ) : ℤ) * 0 by ring, ModularCurve.qExpand_coeff_mul,
          ModularCurve.laurentOfInt_apply, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
          HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          ModularCurve.constantCoeff_tateA4, map_zero]
      have hc40 : (ModularCurve.tateBase L q).c₄.coeff 0 = 1 := by
        rw [hc4def, HahnSeries.coeff_sub', Pi.sub_apply, show (48 : LaurentSeries L) = HahnSeries.C (48 : L) from
          (map_ofNat _ 48).symm, hCmul, ha40, mul_zero, sub_zero, ← hC0 1, map_one]

      obtain ⟨px, hpx⟩ : ∃ px : PowerSeries L, x = HahnSeries.ofPowerSeries ℤ L px := by
        by_cases hv1 : v 1 = 0
        · exact ⟨_, by rw [hxdef, ModularCurve.cuspPoint_of_eq_zero _ hv1, ModularCurve.tateToricPoint_fst]⟩
        · exact ⟨_, by rw [hxdef, ModularCurve.cuspPoint_of_ne_zero _ hv1, ModularCurve.nonToricPoint_fst]⟩
      have hX2 : ((x + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff 0 = (PowerSeries.constantCoeff px + (12 : L)⁻¹) ^ 2 := by
        rw [hpx, ← HahnSeries.ofPowerSeries_C, ← map_add, ← map_pow, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
          HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_add,
          PowerSeries.constantCoeff_C]
      have hβ : (4 : L) * (PowerSeries.constantCoeff px + (12 : L)⁻¹) ^ 2 + (-(12 : L)⁻¹) * 1 = 0 := by
        have := congrArg (fun z : LaurentSeries L => z.coeff 0) hb0
        simp only [HahnSeries.coeff_add', Pi.add_apply] at this
        rw [hCmul, hCmul, hX2, hc40] at this
        exact this
      have hpx0 : (x.coeff 0 : L) = PowerSeries.constantCoeff px := by
        rw [hpx, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      by_cases hv1 : v 1 = 0
      ·
        have hv0' : v 0 ≠ 0 := by
          intro h0'; apply hv0; funext i; fin_cases i <;> simp [h0', hv1]
        set c : L := ((ξu ^ (v 0).val : Lˣ) : L) with hcdef
        have hcξ : c = ξ ^ (v 0).val := by rw [hcdef, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
        have hc1 : c ≠ 1 := by
          rw [hcξ]; intro h1
          have hd := (hξ.pow_eq_one_iff_dvd _).mp h1
          have hlt : (v 0).val < q := ZMod.val_lt _
          have hpos : 0 < (v 0).val := by
            rw [Nat.pos_iff_ne_zero]; exact fun e => hv0' ((ZMod.val_eq_zero _).mp e)
          exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr hlt)
        have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
        have hx0 : x.coeff 0 = c * ((1 - c)⁻¹) ^ 2 := by
          rw [hxdef, ModularCurve.cuspPoint_of_eq_zero _ hv1, ModularCurve.tateToricPoint_fst,
            show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
            if_pos rfl, Ring.inverse_eq_inv']
        rw [← hpx0, hx0] at hβ

        set ω : ℂ := ι c with hω
        have hωN : ω ^ q = 1 := by
          rw [hω, hcξ, ← map_pow, ← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow, map_one]
        have hω1 : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hωN (NeZero.ne _)
        have hωne : 1 - ω ≠ 0 := by
          rw [hω, ← map_one ι, ← map_sub]; exact (map_ne_zero ι).mpr h1c
        have hβ' := congrArg ι hβ
        simp only [map_add, map_mul, map_pow, map_inv₀, map_sub, map_one, map_neg, map_ofNat, map_zero] at hβ'
        rw [← hω] at hβ'

        set t : ℂ := ω * ((1 - ω)⁻¹) ^ 2 with ht
        have hnt : (4 : ℝ)⁻¹ ≤ ‖t‖ := by
          rw [ht, norm_mul, norm_pow, norm_inv, hω1, one_mul]
          have hle : ‖1 - ω‖ ≤ 2 := by
            calc ‖1 - ω‖ ≤ ‖(1 : ℂ)‖ + ‖ω‖ := norm_sub_le _ _
              _ = 2 := by rw [norm_one, hω1]; norm_num
          have hpos : 0 < ‖1 - ω‖ := norm_pos_iff.mpr hωne
          have hge : (2 : ℝ)⁻¹ ≤ ‖1 - ω‖⁻¹ := by rw [inv_le_inv₀ (by norm_num) hpos]; exact hle
          nlinarith [hge]
        have hts : (6 : ℝ)⁻¹ ≤ ‖t + 12⁻¹‖ := by
          have htri : ‖t‖ ≤ ‖t + 12⁻¹‖ + ‖(12 : ℂ)⁻¹‖ := by
            calc ‖t‖ = ‖(t + 12⁻¹) - 12⁻¹‖ := by ring_nf
              _ ≤ ‖t + 12⁻¹‖ + ‖(12 : ℂ)⁻¹‖ := norm_sub_le _ _
          rw [norm_inv, RCLike.norm_ofNat] at htri
          linarith
        have hfin : (4 : ℂ) * (t + 12⁻¹) ^ 2 = 12⁻¹ := by linear_combination hβ'
        have hn := congrArg norm hfin
        rw [norm_mul, norm_pow, norm_inv, RCLike.norm_ofNat, RCLike.norm_ofNat] at hn
        nlinarith [hts, hn]
      ·
        have hj0 : 0 < (v 1).val := by
          rw [Nat.pos_iff_ne_zero]; exact fun e => hv1 ((ZMod.val_eq_zero _).mp e)
        have hjN : (v 1).val < q := ZMod.val_lt _
        have hx0 : x.coeff 0 = 0 := by
          rw [hxdef, ModularCurve.cuspPoint_of_ne_zero _ hv1, ModularCurve.nonToricPoint_fst,
            show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
            PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularCurve.slotSubst]
          have hX0' : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries L) = 0 := PowerSeries.constantCoeff_X
          apply MvPowerSeries.constantCoeff_subst_eq_zero
          · apply MvPowerSeries.hasSubst_of_constantCoeff_zero
            intro s
            fin_cases s <;>
              simp [ModularCurve.slotFamily, map_mul, map_pow, hX0', hj0.ne', (Nat.sub_pos_of_lt hjN).ne']
          · intro s
            fin_cases s <;>
              simp [ModularCurve.slotFamily, map_mul, map_pow, hX0', hj0.ne', (Nat.sub_pos_of_lt hjN).ne']
          · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ModularCurve.tateUnivX_apply]
            simp
        rw [← hpx0, hx0, zero_add] at hβ
        norm_num at hβ
    · show R4GC.ιB ι (x + HahnSeries.C ((12 : L)⁻¹)) * R4GC.qC (⇑(Bw v)) = R4GC.qC (⇑(Aw v))
      rw [hBι, hAι, ← map_mul, hid]
  ·
    intro ρ hρ
    obtain ⟨h4C, h4S⟩ := hS4 ρ hρ
    refine ⟨h4C, hC6s ρ hρ, fun v => ⟨?_, ?_, hRs ρ hρ v⟩⟩
    ·
      dsimp only [Aw]
      simp only [ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ModularForm.coe_mcast, ModularForm.coe_mul]
      rw [SlashAction.add_slash, ModularForm.smul_slash, R4GC.σ_conjElemN_apply, hC6s ρ hρ]
      congr 1
      rw [show (6 : ℤ) = 3 + 3 by norm_num, ModularForm.mul_slash, R4GC.det_conjElemN_val, abs_one, one_smul,
        hRs ρ hρ v]
    ·
      dsimp only [Bw]
      simp only [ModularForm.coe_add, ModularForm.IsGLPos.coe_smul]
      rw [SlashAction.add_slash, ModularForm.smul_slash, ModularForm.smul_slash, R4GC.σ_conjElemN_apply,
        R4GC.σ_conjElemN_apply, h4S v, h4C]

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg
    ∃ (Aw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 3)
      (C4 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C6 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6),
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.cuspPoint L q ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Aw v))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₄ ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₆ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C4 ∧
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C6 ∧
        ∀ v : Fin 2 → ZMod q,
          (⇑(Aw v) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Aw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Bw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)]) ∧
          (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqℓ0 : q * ℓg ≠ 0 := Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero

  have hξ' : IsPrimitiveRoot (ξ ^ ℓg) q := hξ.pow (Nat.pos_of_ne_zero hqℓ0) (mul_comm q ℓg)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hℓC : (ℓg : ℂ) ≠ 0 := by exact_mod_cast hℓg.ne_zero
  have hι' : ι (ξ ^ ℓg) = Complex.exp (2 * Real.pi * Complex.I / q) := by
    rw [map_pow, hι, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  obtain ⟨Aw, Bw, Rw, C4, C6, hv, hC4, hC6, hsl⟩ := cuspForms_levelH q M' hqM' L (ξ ^ ℓg) hξ' ι hι'

  have hu : (hξ.isUnit hqℓ0).unit ^ ℓg = (hξ'.isUnit (Fact.out : q.Prime).ne_zero).unit := by
    ext; rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, IsUnit.unit_spec]

  have hle : ((CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
    apply Subgroup.map_mono
    rw [hH₁]
    exact ModularCurve.GammaH_mono inf_le_left
  rw [hu]
  exact ⟨fun v => ModularCurve.restrictForm hle (Aw v), fun v => ModularCurve.restrictForm hle (Bw v),
    fun v => ModularCurve.restrictForm hle (Rw v), ModularCurve.restrictForm hle C4, ModularCurve.restrictForm hle C6,
    hv, hC4, hC6, hsl⟩

end S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq (solution)
