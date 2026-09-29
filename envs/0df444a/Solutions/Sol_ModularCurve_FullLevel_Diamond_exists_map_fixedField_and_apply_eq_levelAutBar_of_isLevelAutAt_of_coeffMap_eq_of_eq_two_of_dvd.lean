-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/210f60d9-0acf-563e-8593-8bd6fa356de7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000

noncomputable section

namespace W1DI
variable (m : ℕ) [NeZero m]

theorem mpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
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

section GH
variable (m : ℕ) [NeZero m] (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

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

scoped instance GH_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] : (GH m M').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

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

end GH

section Pair

variable {q : ℕ} [NeZero q] {M' : ℕ} {ℓ : ℕ} [NeZero ℓ]

theorem Dr_mul_Dr : Dr (q * ℓ) = Dr q * Dr ℓ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ell_dvd_of_mem {γ' : SL(2, ℤ)} (h : γ' ∈ GH (q * ℓ) M') : (ℓ : ℤ) ∣ γ' 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff γ').mp h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans ⟨q * q * ℓ * M', by push_cast; ring⟩ h10

theorem upSL_mem {γ' : SL(2, ℤ)} (h : γ' ∈ GH (q * ℓ) M') : upSL (m := ℓ) γ' (ell_dvd_of_mem h) ∈ GH q M' := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff γ').mp h
  rw [mem_GH_iff]
  constructor
  · show ((γ' 1 0 / ℓ : ℤ) : ZMod (q ^ 2 * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    obtain ⟨c, hc⟩ := h10
    rw [hc]
    refine ⟨ℓ * c, ?_⟩
    push_cast
    rw [show ((q : ℤ) * ℓ) ^ 2 * M' * c = ℓ * ((q : ℤ) ^ 2 * M' * (ℓ * c)) by ring,
      Int.mul_ediv_cancel_left _ (mneZ ℓ)]
  · show ((γ' 1 1 : ℤ) : ZMod q) = 1
    have := congrArg (ZMod.castHom (dvd_mul_right q ℓ) (ZMod q)) h11
    rwa [map_intCast, map_one] at this

theorem le_conj_ell : Γ (q * ℓ) M' ≤ ConjAct.toConjAct (Dr ℓ)⁻¹ • Γ q M' := by
  rintro x ⟨γ', hγ', rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨upSL γ' (ell_dvd_of_mem hγ'), upSL_mem hγ', ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact upSL_coe γ' _

end Pair

section SlashSec

open UpperHalfPlane

variable {m : ℕ} [NeZero m] {M' : ℕ}

variable (hmM' : Nat.Coprime m M')
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ModularForm (Γ m M') k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

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

end SlashSec

section QExp

open UpperHalfPlane HahnSeries

variable {m : ℕ} [NeZero m] {M' : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ m M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem qC_sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {g : ModularForm (Γ m M') k}
    (hg : g ≠ 0) : qC (sl hmM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hmM' γ hγ hg ((qC_eq_zero_iff _).mp h)

end QExp

section Emb

open UpperHalfPlane HahnSeries

variable {L : Type} [Field L] [CharZero L]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

theorem coeffMap_injective_of_injective : Function.Injective (coeffMap ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

theorem coeffMap_coeffEmb' (x : LaurentSeries ℚ) : coeffMap ι₀ (coeffEmb L x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ne_zero_of_intSeriesC {m : ℕ} [NeZero m] {M' : ℕ} {k : ℤ} {g : ModularForm (Γ m M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {m : ℕ} [NeZero m] {M' : ℕ} {k : ℤ} {g : ModularForm (Γ m M') k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases hdvd : (n : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hdvd, qExpand_coeff_of_not_dvd n _ hdvd, map_zero]

abbrev en (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem exists_emb_bar {n : ℕ} (hn : 0 < n) {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z n) :
    ∃ ι : AlgebraicClosure ℚ →+* ℂ, ι z = en n := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  have hmin : minpoly ℚ z = Polynomial.cyclotomic n ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hz hn).symm
  have hroot : en n ∈ (minpoly ℚ z).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp n hn0)).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ z] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem en_mul_pow {q ℓ : ℕ} (hq : q ≠ 0) (hℓ : ℓ ≠ 0) : en (q * ℓ) ^ ℓ = en q := by
  rw [en, en, ← Complex.exp_nat_mul]
  congr 1
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  push_cast
  field_simp

end Emb

section Closure

open IntermediateField

theorem mem_fixedField_closure_iff {F E : Type*} [Field F] [Field E] [Algebra F E] (S : Set (E ≃ₐ[F] E)) (w : E) :
    w ∈ fixedField (Subgroup.closure S) ↔ ∀ τ ∈ S, τ w = w := by
  rw [mem_fixedField_iff]
  constructor
  · intro h τ hτ
    exact h τ (Subgroup.subset_closure hτ)
  · intro h τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ => exact h σ hσ
    | one => rfl
    | mul σ σ' _ _ h1 h2 => rw [AlgEquiv.mul_apply, h2, h1]
    | inv σ _ h1 =>
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← h1]
        exact σ.symm_apply_apply w

variable {k : Type} [Field k] (K : IntermediateField k (LaurentSeries k))
  (K₀ : IntermediateField k ↥K) {X : Type} [Field X] (A B : ↥K₀ →+* X)

def R (x : LaurentSeries k) : Prop :=
  ∃ hK : x ∈ K, ∃ h₀ : (⟨x, hK⟩ : ↥K) ∈ K₀, A ⟨⟨x, hK⟩, h₀⟩ = B ⟨⟨x, hK⟩, h₀⟩

variable {K K₀ A B}

theorem R.apply_eq {x : LaurentSeries k} (h : R K K₀ A B x) (w : ↥K₀)
    (hw : ((w : ↥K) : LaurentSeries k) = x) : A w = B w := by
  obtain ⟨hK, h₀, e⟩ := h
  have : w = ⟨⟨x, hK⟩, h₀⟩ := Subtype.ext (Subtype.ext hw)
  rw [this]; exact e

theorem R.mk' {x : LaurentSeries k} (hK : x ∈ K) (h₀ : (⟨x, hK⟩ : ↥K) ∈ K₀)
    (e : ∀ (h₁ : x ∈ K) (h₂ : (⟨x, h₁⟩ : ↥K) ∈ K₀), A ⟨⟨x, h₁⟩, h₂⟩ = B ⟨⟨x, h₁⟩, h₂⟩) : R K K₀ A B x :=
  ⟨hK, h₀, e hK h₀⟩

theorem R.add {x y : LaurentSeries k} (hx : R K K₀ A B x) (hy : R K K₀ A B y) : R K K₀ A B (x + y) := by
  obtain ⟨hxK, hx₀, ex⟩ := hx
  obtain ⟨hyK, hy₀, ey⟩ := hy
  have hK : x + y ∈ K := add_mem hxK hyK
  have e1 : (⟨x + y, hK⟩ : ↥K) = ⟨x, hxK⟩ + ⟨y, hyK⟩ := Subtype.ext rfl
  have h₀ : (⟨x + y, hK⟩ : ↥K) ∈ K₀ := by rw [e1]; exact add_mem hx₀ hy₀
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨x + y, hK⟩, h₀⟩ : ↥K₀) = ⟨⟨x, hxK⟩, hx₀⟩ + ⟨⟨y, hyK⟩, hy₀⟩ := Subtype.ext e1
  rw [e2, map_add, map_add, ex, ey]

theorem R.mul {x y : LaurentSeries k} (hx : R K K₀ A B x) (hy : R K K₀ A B y) : R K K₀ A B (x * y) := by
  obtain ⟨hxK, hx₀, ex⟩ := hx
  obtain ⟨hyK, hy₀, ey⟩ := hy
  have hK : x * y ∈ K := mul_mem hxK hyK
  have e1 : (⟨x * y, hK⟩ : ↥K) = ⟨x, hxK⟩ * ⟨y, hyK⟩ := Subtype.ext rfl
  have h₀ : (⟨x * y, hK⟩ : ↥K) ∈ K₀ := by rw [e1]; exact mul_mem hx₀ hy₀
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨x * y, hK⟩, h₀⟩ : ↥K₀) = ⟨⟨x, hxK⟩, hx₀⟩ * ⟨⟨y, hyK⟩, hy₀⟩ := Subtype.ext e1
  rw [e2, map_mul, map_mul, ex, ey]

theorem R.neg {x : LaurentSeries k} (hx : R K K₀ A B x) : R K K₀ A B (-x) := by
  obtain ⟨hxK, hx₀, ex⟩ := hx
  have hK : -x ∈ K := neg_mem hxK
  have e1 : (⟨-x, hK⟩ : ↥K) = -⟨x, hxK⟩ := Subtype.ext rfl
  have h₀ : (⟨-x, hK⟩ : ↥K) ∈ K₀ := by rw [e1]; exact neg_mem hx₀
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨-x, hK⟩, h₀⟩ : ↥K₀) = -⟨⟨x, hxK⟩, hx₀⟩ := Subtype.ext e1
  rw [e2, map_neg, map_neg, ex]

theorem R.inv {x : LaurentSeries k} (hx : R K K₀ A B x) : R K K₀ A B x⁻¹ := by
  obtain ⟨hxK, hx₀, ex⟩ := hx
  have hK : x⁻¹ ∈ K := inv_mem hxK
  have e1 : (⟨x⁻¹, hK⟩ : ↥K) = (⟨x, hxK⟩ : ↥K)⁻¹ := Subtype.ext rfl
  have h₀ : (⟨x⁻¹, hK⟩ : ↥K) ∈ K₀ := by rw [e1]; exact inv_mem hx₀
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨x⁻¹, hK⟩, h₀⟩ : ↥K₀) = (⟨⟨x, hxK⟩, hx₀⟩ : ↥K₀)⁻¹ := Subtype.ext e1
  rw [e2, map_inv₀, map_inv₀, ex]

theorem R.one : R K K₀ A B (1 : LaurentSeries k) := by
  have hK : (1 : LaurentSeries k) ∈ K := one_mem _
  have e1 : (⟨1, hK⟩ : ↥K) = 1 := Subtype.ext rfl
  have h₀ : (⟨1, hK⟩ : ↥K) ∈ K₀ := by rw [e1]; exact one_mem _
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨1, hK⟩, h₀⟩ : ↥K₀) = 1 := Subtype.ext e1
  rw [e2, map_one, map_one]

theorem R_algebraMap (hAB : ∀ c : k, A (algebraMap k ↥K₀ c) = B (algebraMap k ↥K₀ c)) (c : k) :
    R K K₀ A B (algebraMap k (LaurentSeries k) c) := by
  have hK : algebraMap k (LaurentSeries k) c ∈ K := IntermediateField.algebraMap_mem _ _
  have e1 : (⟨algebraMap k (LaurentSeries k) c, hK⟩ : ↥K) = algebraMap k ↥K c := Subtype.ext rfl
  have h₀ : (⟨algebraMap k (LaurentSeries k) c, hK⟩ : ↥K) ∈ K₀ := by
    rw [e1]; exact IntermediateField.algebraMap_mem _ _
  refine ⟨hK, h₀, ?_⟩
  have e2 : (⟨⟨algebraMap k (LaurentSeries k) c, hK⟩, h₀⟩ : ↥K₀) = algebraMap k ↥K₀ c := Subtype.ext e1
  rw [e2]
  exact hAB c

theorem R.of_mem_closure {S : Set (LaurentSeries k)} (hgen : ∀ x ∈ S, R K K₀ A B x)
    (hAB : ∀ c : k, A (algebraMap k ↥K₀ c) = B (algebraMap k ↥K₀ c)) {x : LaurentSeries k}
    (hx : x ∈ Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ S)) : R K K₀ A B x := by
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | hy
      · exact R_algebraMap hAB c
      · exact hgen y hy
  | one => exact R.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

theorem laurentBaseChange_le_closure (L : Type) [Field L] [CharZero L] (Γ₀ : Subgroup SL(2, ℤ)) :
    ∀ x : LaurentSeries L, x ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ₀) →
      x ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ (⇑(coeffEmb L) '' intFormRatiosC ℚ Γ₀)) := by
  intro x hx
  rw [mem_laurentBaseChange_iff] at hx
  refine Subfield.closure_le.mpr ?_ hx
  rintro y (⟨c, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  ·
    change z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ₀) at hz
    induction hz using Subfield.closure_induction with
    | mem w hw =>
        rcases hw with ⟨r, rfl⟩ | hw
        · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
          exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
        · exact Subfield.subset_closure (Or.inr ⟨w, hw, rfl⟩)
    | one => rw [map_one]; exact one_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Closure

end W1DI
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd.W1DI"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd.W1DI"

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup IntermediateField HahnSeries W1DI
open scoped MatrixGroups ModularForm

theorem W1DI.GammaH_coe_mono (N : ℕ) {H' H : Subgroup (ZMod N)ˣ} (h : H' ≤ H) :
    ((CohCarrier.GammaH N H' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  have hle : CohCarrier.GammaH N H' ≤ CohCarrier.GammaH N H := by
    intro A hA
    rw [CohCarrier.mem_GammaH_iff] at hA ⊢
    exact ⟨hA.1, h hA.2⟩
  exact Subgroup.map_mono hle

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 25600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (G : Subgroup (↥K ≃ₐ[↥k₀] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[↥k₀] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ K τ})
    (K₀ : IntermediateField ↥k₀ ↥K) (hK₀ : K₀ = IntermediateField.fixedField G) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀,
        ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) →
    ∀ (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀),

      (∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥K)) : LaurentSeries ↥k₀) =
        (                                ((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) →

      (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' q → ζ.val = (((ξ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥K ≃ₐ[↥k₀] ↥K),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ' q (q ^ 2 * M') H₁ γ K τ →
          ∃ hτ : ∀ f : ↥K, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥K), hτ (f : ↥K) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))) := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀ φ hφ1 ζ ξ' hξ' hζ γ hγ τ hτ

  have hqP : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hqP.ne_zero
  have hqpos : 0 < q := hqP.pos
  have hcopq : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd hqP).2 hqM'
  haveI : Fact ℓg.Prime := ⟨hℓg⟩
  let incl : ↥k₀ →+* AlgebraicClosure ℚ := algebraMap ↥k₀ (AlgebraicClosure ℚ)

  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by
    have hξb : IsPrimitiveRoot (ξ : AlgebraicClosure ℚ) q :=
      hξ.map_of_injective (f := incl) Subtype.val_injective
    obtain ⟨ι, hι⟩ := exists_emb_bar hqpos hξb
    exact ⟨ι.comp incl, by rw [RingHom.comp_apply]; change ι (ξ : AlgebraicClosure ℚ) = _; rw [hι, en]⟩

  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker
    ↥k₀ q M' hqM' ℓg hℓgM' ξ ξ' hξ hξ' H₁ hH₁ K
  obtain ⟨γ', hγ'0, -, -, hτ'⟩ := hd γ hγ τ hτ
  have hnorm := ModularCurve.FullLevel.AuxLevelOne.mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0_of_dvd
    q M' hqM' ℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ K hK G hG K₀ hK₀ γ'⁻¹ (inv_mem hγ'0) τ (by rw [inv_inv]; exact hτ')
  have hτK₀ : ∀ f : ↥K, f ∈ K₀ → τ f ∈ K₀ := hnorm.2.2.1
  refine ⟨hτK₀, ?_⟩

  obtain ⟨hBK, hfix⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
      q M' hqM' ℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ K hK
  have hK₀' : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries ↥k₀,
      x ∈ laurentBaseChange ↥k₀ (xHFunctionField (q ^ 2 * M') (levelH q M')) ∧
        ((w : ↥K) : LaurentSeries ↥k₀) = x := by
    intro w
    rw [hK₀, hG, mem_fixedField_closure_iff, ← hfix w]
    constructor
    · intro h γ₁ hγ₁ hγ₁0 τ₁ hτ₁
      exact h τ₁ ⟨γ₁, hγ₁, hγ₁0, hτ₁⟩
    · rintro h τ₁ ⟨γ₁, hγ₁, hγ₁0, hτ₁⟩
      exact h γ₁ hγ₁ hγ₁0 τ₁ hτ₁

  set Λ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') := levelAutBar q M' ζ γ with hΛdef
  have hΛ : IsLevelAutBar q M' ζ γ Λ :=
    isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ γ hγ)

  let τ₀ : ↥K₀ →+* ↥K₀ :=
    { toFun := fun f => ⟨τ (f : ↥K), hτK₀ (f : ↥K) f.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun f g => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun f g => Subtype.ext (by simp) }
  have hτ₀ : ∀ f : ↥K₀, ((τ₀ f : ↥K₀) : ↥K) = τ (f : ↥K) := fun f => rfl
  let A : ↥K₀ →+* LaurentSeries (AlgebraicClosure ℚ) :=
    { toFun := fun f => (((φ (τ₀ f) : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
      map_one' := by simp
      map_mul' := fun f g => by simp
      map_zero' := by simp
      map_add' := fun f g => by simp }
  have hA : ∀ f : ↥K₀, A f = (((φ ⟨τ (f : ↥K), hτK₀ (f : ↥K) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) :
      LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl
  let B : ↥K₀ →+* LaurentSeries (AlgebraicClosure ℚ) :=
    { toFun := fun f => ((Λ ((φ f : ↥F₀) : ↥(fieldBar q M')) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
      map_one' := by simp
      map_mul' := fun f g => by simp
      map_zero' := by simp
      map_add' := fun f g => by simp }
  have hB : ∀ f : ↥K₀, B f = ((Λ ((φ f : ↥F₀) : ↥(fieldBar q M')) : ↥(fieldBar q M')) :
      LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl

  have hAB : ∀ c : ↥k₀, A (algebraMap ↥k₀ ↥K₀ c) = B (algebraMap ↥k₀ ↥K₀ c) := by
    intro c
    have e1 : τ₀ (algebraMap ↥k₀ ↥K₀ c) = algebraMap ↥k₀ ↥K₀ c := by
      apply Subtype.ext
      rw [hτ₀]
      exact τ.commutes c
    have e2 : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (incl c) := rfl
    rw [hA, hB]
    change (((φ (τ₀ (algebraMap ↥k₀ ↥K₀ c)) : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [e1, φ.commutes, e2, Λ.commutes]

  have hφx : ∀ (w : ↥K₀) (x : LaurentSeries ↥k₀), ((w : ↥K) : LaurentSeries ↥k₀) = x →
      (((φ w : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap incl x := by
    intro w x hw
    have h1 := hφ1 w
    rw [hw] at h1
    exact h1.symm

  have hξ'b : IsPrimitiveRoot (ξ' : AlgebraicClosure ℚ) q :=
    hξ'.map_of_injective (f := incl) Subtype.val_injective
  obtain ⟨ι, hιξ'⟩ := exists_emb_bar hqpos hξ'b
  have hιζ : ι ζ.val = Complex.exp (2 * Real.pi * Complex.I / q) := by
    rw [hζ]
    exact hιξ'
  have hι'ξ' : (ι.comp incl) ξ' = Complex.exp (2 * Real.pi * Complex.I / (q : ℕ)) := hιξ'

  have hH₁le : H₁ ≤ levelH q M' := by rw [hH₁]; exact inf_le_left
  have hle₁ : ((CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ q M' :=
    W1DI.GammaH_coe_mono (q ^ 2 * M') hH₁le

  have hgen : ∀ x ∈ (⇑(coeffEmb ↥k₀) '' intFormRatiosC ℚ (GH q M')), R K K₀ A B x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy

    set f' : ModularForm ((CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
      restrictForm hle₁ f with hf'def
    set g' : ModularForm ((CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
      restrictForm hle₁ g with hg'def
    have hcf : (⇑f' : UpperHalfPlane → ℂ) = ⇑f := by rw [hf'def]; exact coe_restrictForm hle₁ f
    have hcg : (⇑g' : UpperHalfPlane → ℂ) = ⇑g := by rw [hg'def]; exact coe_restrictForm hle₁ g
    have hf' : IsIntegralQExp f' pf := by rw [hcf]; exact hf
    have hg' : IsIntegralQExp g' pg := by rw [hcg]; exact hg

    have hxK : coeffEmb ↥k₀ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ K := by
      rw [hK]
      exact coeffEmb_mem_laurentBaseChange ↥k₀ (div_mem_qExpFunctionFieldC f' g' hf' hg' hg0)
    have hxB : coeffEmb ↥k₀ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈
        laurentBaseChange ↥k₀ (xHFunctionField (q ^ 2 * M') (levelH q M')) :=
      coeffEmb_mem_laurentBaseChange ↥k₀ (div_mem_qExpFunctionFieldC f g hf hg hg0)
    have hx₀ : (⟨_, hxK⟩ : ↥K) ∈ K₀ := (hK₀' _).mpr ⟨_, hxB, rfl⟩
    refine R.mk' hxK hx₀ fun h₁ h₂ => ?_
    set w₀ : ↥K₀ := ⟨⟨coeffEmb ↥k₀ (intSeriesC ℚ pf / intSeriesC ℚ pg), h₁⟩, h₂⟩ with hw₀def
    have hw : (((w₀ : ↥K₀) : ↥K) : LaurentSeries ↥k₀) =
        coeffEmb ↥k₀ (intSeriesC ℚ pf / intSeriesC ℚ pg) := rfl

    have hφw : (((φ w₀ : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
      rw [hφx w₀ (coeffEmb ↥k₀ (intSeriesC ℚ pf / intSeriesC ℚ pg)) rfl, coeffEmb, coeffEmb, coeffMap_coeffMap]
      exact coeffMap_congr (Subsingleton.elim _ _) _
    have hφw' : ((φ w₀ : ↥F₀) : ↥(fieldBar q M')) =
        ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :=
      Subtype.ext hφw

    have hΛfg := hΛ k f g pf pg hf hg hg0 ι hιζ
    rw [← hφw'] at hΛfg
    change coeffMap ι ((Λ ((φ w₀ : ↥F₀) : ↥(fieldBar q M')) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) *
      qC (⇑g ∣[k] conjElemN q γ) = qC (⇑f ∣[k] conjElemN q γ) at hΛfg

    have key := hτ k f' g' pf pg hf' hg' hg0 (w₀ : ↥K) hw (ι.comp incl) hι'ξ'
    rw [hcf, hcg] at key
    change coeffMap (ι.comp incl) ((τ (w₀ : ↥K) : ↥K) : LaurentSeries ↥k₀) *
      qC (⇑g ∣[k] conjElemN q γ) = qC (⇑f ∣[k] conjElemN q γ) at key

    have hne : qC (⇑g ∣[k] conjElemN q γ) ≠ 0 := by
      rw [← coe_sl hcopq γ hγ]
      exact qC_sl_ne_zero hcopq γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0)
    have heq : coeffMap (ι.comp incl) ((τ (w₀ : ↥K) : ↥K) : LaurentSeries ↥k₀) =
        coeffMap ι ((Λ ((φ w₀ : ↥F₀) : ↥(fieldBar q M')) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) :=
      mul_right_cancel₀ hne (key.trans hΛfg.symm)

    have hτw : coeffMap (ι.comp incl) ((τ (w₀ : ↥K) : ↥K) : LaurentSeries ↥k₀) = coeffMap ι (A w₀) := by
      rw [← coeffMap_coeffMap, hA]
      congr 1
      exact hφ1 ⟨τ (w₀ : ↥K), hτK₀ _ w₀.2⟩
    rw [hτw] at heq
    have h4 := coeffMap_injective_of_injective ι heq
    rw [h4, hB]

  intro f
  obtain ⟨x, hxB, hfx⟩ := (hK₀' (f : ↥K)).mp f.2
  have hxcl := laurentBaseChange_le_closure ↥k₀ (GH q M') x hxB
  have hR : R K K₀ A B x := R.of_mem_closure hgen hAB hxcl
  have := hR.apply_eq f hfx
  rw [hA, hB] at this
  exact Subtype.ext this

end S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_two_of_dvd (solution)
