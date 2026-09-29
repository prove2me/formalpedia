-- Prove2me | solution 1 for ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e5266bd1-a7d8-5d98-bb90-2657411e7016

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma
import Theorems.Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul

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

end R4GC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLE
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

end GH
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

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

theorem q_dvd_01 {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) : (q : ℤ) ∣ δ 0 1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hδ).2.1

variable (hqM' : Nat.Coprime q M')
include hqM'

theorem downSL_mem {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) (hδ0 : δ ∈ Gamma0 M') :
    downSL (m := q) δ (q_dvd_01 hδ) ∈ GH q M' := by
  obtain ⟨-, -, h10, h11⟩ := Gamma_mem.mp hδ
  rw [mem_GH_iff]
  refine ⟨?_, h11⟩
  show ((((q : ℤ) * δ 1 0 : ℤ)) : ZMod (q ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (q : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hM : (M' : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ0)
  have hcop : IsCoprime (q : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hqM'
  obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
  exact ⟨c, by rw [hc]; push_cast; ring⟩

omit hqM' in
theorem conjElemN_eq_downSL {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) :
    conjElemN q δ = ((downSL (m := q) δ (q_dvd_01 hδ) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [conjElemN_eq, mul_assoc, ← downSL_coe δ (q_dvd_01 hδ), inv_mul_cancel_left]

theorem slash_Dr_slash_conjElemN {k : ℤ} (f : ModularForm (Γ q M') k) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma q) (hδ0 : δ ∈ Gamma0 M') :
    ((⇑f : UpperHalfPlane → ℂ) ∣[k] Dr ℓ) ∣[k] conjElemN (q * ℓ) δ = (⇑f : UpperHalfPlane → ℂ) ∣[k] Dr ℓ := by
  have hgrp : Dr ℓ * conjElemN (q * ℓ) δ = conjElemN q δ * Dr ℓ := by
    rw [conjElemN_eq, conjElemN_eq, Dr_mul_Dr]; group
  rw [← SlashAction.slash_mul, hgrp, SlashAction.slash_mul, conjElemN_eq_downSL hδ]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (downSL_mem hqM' hδ hδ0))

end Pair
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

section Stretch

open UpperHalfPlane Function

variable {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} [Γ₁.FiniteIndex] {ℓ : ℕ} {k : ℤ}
variable (hle : (Γ₂ : Subgroup (GL (Fin 2) ℝ)) ≤
  ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • (Γ₁ : Subgroup (GL (Fin 2) ℝ)))

def stretch (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Γ₂ : Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ • restrictForm hle (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem coe_stretch_eq_smul (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(stretch hle hℓ f) : ℍ → ℂ) =
      ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
  rw [stretch, ModularForm.IsGLPos.coe_smul, coe_restrictForm, ModularForm.coe_translate]

theorem stretch_apply (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    stretch hle hℓ f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hpk : ((ℓ : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ)
  have := congrFun (coe_stretch_eq_smul hle hℓ f) τ
  rw [this, Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply k hℓ, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hpk, one_mul]

theorem coe_stretch (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(stretch hle hℓ f) : ℍ → ℂ) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (stretch_apply hle hℓ f)

private theorem _root_.W1xLE.periodic_comp_ofComplex (hT : ModularGroup.T ∈ Γ₁)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) 1 := by
  have h1 : (1 : ℝ) ∈ (Γ₁ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples 1
  exact SlashInvariantFormClass.periodic_comp_ofComplex f h1

p2m_export "W1xLE" "periodic_comp_ofComplex"

theorem qCoeff_stretch (hT : ModularGroup.T ∈ Γ₁) (hℓ : ℓ ≠ 0)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hle hℓ f)) n
      = if ℓ ∣ n then ModularFormClass.qCoeff (⇑f) (n / ℓ) else 0 := by
  rw [coe_stretch]
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul (periodic_comp_ofComplex hT f) f.holo'
    (ModularFormClass.bdd_at_infty f) hℓ n

def expandPS (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

@[scoped simp] theorem coeff_expandPS (ℓ : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 :=
  PowerSeries.coeff_mk _ _

theorem isIntegralQExp_stretch (hT : ModularGroup.T ∈ Γ₁) (hℓ : ℓ ≠ 0)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) {p : PowerSeries ℤ}
    (hp : ModularCurve.IsIntegralQExp f p) :
    ModularCurve.IsIntegralQExp (stretch hle hℓ f) (expandPS ℓ p) := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  have h := qCoeff_stretch hle hT hℓ f n
  simp only [ModularFormClass.qCoeff] at h
  rw [h, coeff_expandPS]
  split_ifs with hdvd
  · exact hp.coeff (n / ℓ)
  · simp

theorem intSeriesC_expandPS (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] (p : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (expandPS ℓ p)
      = ModularCurve.qExpand K ℓ (ModularCurve.intSeriesC K p) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  ext m
  simp only [ModularCurve.intSeriesC]
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hm' : m' < 0
    · have : (ℓ : ℤ) * m' < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hℓ) hm'
      rw [if_pos this, if_pos hm']
    · have hm'0 : 0 ≤ m' := le_of_not_gt hm'
      have hprod : ¬ (ℓ : ℤ) * m' < 0 := not_lt.mpr (mul_nonneg (by positivity) hm'0)
      rw [if_neg hprod, if_neg hm', PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_expandPS]
      have habs : ((ℓ : ℤ) * m').natAbs = ℓ * m'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, if_pos (dvd_mul_right ℓ _), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [PowerSeries.coeff_map, coeff_expandPS]
      have : ¬ ℓ ∣ m.natAbs := by
        intro h
        apply hdvd
        have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [← Int.natAbs_of_nonneg hm0]
        exact_mod_cast h
      rw [if_neg this, map_zero]

end Stretch
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

section Emb

open UpperHalfPlane HahnSeries

variable {L : Type} [Field L] [CharZero L]

private def _root_.W1xLE.qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

p2m_export "W1xLE" "qC"

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

private abbrev _root_.W1xLE.ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

p2m_export "W1xLE" "ιB"
private theorem _root_.W1xLE.ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

p2m_export "W1xLE" "ιB_injective"
theorem ιB_coeffEmb (x : LaurentSeries ℚ) : ιB ι₀ (coeffEmb L x) = ιC x := by
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

abbrev eq (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

variable {m : ℕ} [NeZero m]

variable (L) in
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

end Emb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

section Main

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [NeZero q] {M' : ℕ} {ℓ : ℕ} [NeZero ℓ] (hqM' : Nat.Coprime q M')
  {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq (q * ℓ))

private abbrev _root_.W1xLE.KL (L : Type) [Field L] [CharZero L] (q ℓ M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M'))

p2m_export "W1xLE" "KL"
variable (q M' ℓ) in

def P (x : LaurentSeries L) : Prop :=
  qExpand L ℓ x ∈ KL L q ℓ M' ∧
    ∀ w : KL L q ℓ M', (w : LaurentSeries L) = qExpand L ℓ x →
      ∀ γ : SL(2, ℤ), γ ∈ Gamma q → γ ∈ Gamma0 M' →
        ∀ τ : KL L q ℓ M' ≃ₐ[L] KL L q ℓ M',
          IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L q ℓ M') τ →
            τ w = w

variable {ξ}

theorem P.mk' {x : LaurentSeries L} (hmem : qExpand L ℓ x ∈ KL L q ℓ M')
    (hfix : ∀ γ : SL(2, ℤ), γ ∈ Gamma q → γ ∈ Gamma0 M' →
        ∀ τ : KL L q ℓ M' ≃ₐ[L] KL L q ℓ M',
          IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L q ℓ M') τ →
            τ ⟨qExpand L ℓ x, hmem⟩ = ⟨qExpand L ℓ x, hmem⟩) :
    P q M' ℓ ξ x := by
  refine ⟨hmem, fun w hw γ hγ hγ0 τ hτ => ?_⟩
  have e : w = ⟨qExpand L ℓ x, hmem⟩ := Subtype.ext hw
  rw [e]
  exact hfix γ hγ hγ0 τ hτ

theorem P.add {x y : LaurentSeries L} (hx : P q M' ℓ ξ x) (hy : P q M' ℓ ξ y) : P q M' ℓ ξ (x + y) := by
  have hmem : qExpand L ℓ (x + y) ∈ KL L q ℓ M' := by rw [map_add]; exact add_mem hx.1 hy.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (x + y), hmem⟩ : KL L q ℓ M') = ⟨qExpand L ℓ x, hx.1⟩ + ⟨qExpand L ℓ y, hy.1⟩ :=
    Subtype.ext (by simp [map_add])
  rw [e, map_add, hx.2 _ rfl γ hγ hγ0 τ hτ, hy.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.mul {x y : LaurentSeries L} (hx : P q M' ℓ ξ x) (hy : P q M' ℓ ξ y) : P q M' ℓ ξ (x * y) := by
  have hmem : qExpand L ℓ (x * y) ∈ KL L q ℓ M' := by rw [map_mul]; exact mul_mem hx.1 hy.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (x * y), hmem⟩ : KL L q ℓ M') = ⟨qExpand L ℓ x, hx.1⟩ * ⟨qExpand L ℓ y, hy.1⟩ :=
    Subtype.ext (by simp [map_mul])
  rw [e, map_mul, hx.2 _ rfl γ hγ hγ0 τ hτ, hy.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.neg {x : LaurentSeries L} (hx : P q M' ℓ ξ x) : P q M' ℓ ξ (-x) := by
  have hmem : qExpand L ℓ (-x) ∈ KL L q ℓ M' := by rw [map_neg]; exact neg_mem hx.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (-x), hmem⟩ : KL L q ℓ M') = -⟨qExpand L ℓ x, hx.1⟩ :=
    Subtype.ext (by simp [map_neg])
  rw [e, map_neg, hx.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.inv {x : LaurentSeries L} (hx : P q M' ℓ ξ x) : P q M' ℓ ξ x⁻¹ := by
  have hmem : qExpand L ℓ x⁻¹ ∈ KL L q ℓ M' := by rw [map_inv₀]; exact inv_mem hx.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ x⁻¹, hmem⟩ : KL L q ℓ M') = (⟨qExpand L ℓ x, hx.1⟩ : KL L q ℓ M')⁻¹ :=
    Subtype.ext (by simp [map_inv₀])
  rw [e, map_inv₀, hx.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.one : P q M' ℓ ξ (1 : LaurentSeries L) := by
  have hmem : qExpand L ℓ (1 : LaurentSeries L) ∈ KL L q ℓ M' := by rw [map_one]; exact one_mem _
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ 1, hmem⟩ : KL L q ℓ M') = 1 := Subtype.ext (by simp)
  rw [e, map_one]

theorem P_algebraMap (c : L) : P q M' ℓ ξ (algebraMap L (LaurentSeries L) c) := by
  have hq : qExpand L ℓ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c := by
    rw [← C_eq_algebraMap, qExpand_C]
  have hmem : qExpand L ℓ (algebraMap L (LaurentSeries L) c) ∈ KL L q ℓ M' := by
    rw [hq]; exact IntermediateField.algebraMap_mem _ _
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (algebraMap L (LaurentSeries L) c), hmem⟩ : KL L q ℓ M') =
      algebraMap L (KL L q ℓ M') c :=
    Subtype.ext (by change qExpand L ℓ (algebraMap L (LaurentSeries L) c) = _; rw [hq]; rfl)
  rw [e, AlgEquiv.commutes]

section Gen

variable [NeZero M']
include hqM' hι₀

theorem P.gen {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH q M')) : P q M' ℓ ξ (coeffEmb L y) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy

  set f' : ModularForm (Γ (q * ℓ) M') k := stretch le_conj_ell hℓ f with hf'def
  set g' : ModularForm (Γ (q * ℓ) M') k := stretch le_conj_ell hℓ g with hg'def
  have hT : ModularGroup.T ∈ GH q M' := translation_mem_GammaH _ _
  have hf' : IsIntegralQExp f' (expandPS ℓ pf) := isIntegralQExp_stretch le_conj_ell hT hℓ f hf
  have hg' : IsIntegralQExp g' (expandPS ℓ pg) := isIntegralQExp_stretch le_conj_ell hT hℓ g hg
  have hg0' : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (ModularCurve.qExpand_injective ℓ (by rw [h, map_zero]))
  have hser : qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) =
      coeffEmb L (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)) := by
    rw [← ModularCurve.coeffEmb_qExpand, map_div₀, intSeriesC_expandPS, intSeriesC_expandPS]
  have hmem : qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) ∈ KL L q ℓ M' := by
    rw [hser]
    exact coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f' g' hf' hg' hg0')
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  set w : KL L q ℓ M' := ⟨qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)), hmem⟩ with hwdef
  have hw : ((w : KL L q ℓ M') : LaurentSeries L) =
      coeffEmb L (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)) := hser

  have key := hτ k f' g' (expandPS ℓ pf) (expandPS ℓ pg) hf' hg' hg0' w hw ι₀ hι₀

  have hinvf : ((⇑f' : ℍ → ℂ) ∣[k] conjElemN (q * ℓ) γ⁻¹) = ⇑f' := by
    rw [hf'def, coe_stretch_eq_smul, ModularForm.smul_slash, σ_conjElemN_apply,
      slash_Dr_slash_conjElemN hqM' f (inv_mem hγ) (inv_mem hγ0)]
  have hinvg : ((⇑g' : ℍ → ℂ) ∣[k] conjElemN (q * ℓ) γ⁻¹) = ⇑g' := by
    rw [hg'def, coe_stretch_eq_smul, ModularForm.smul_slash, σ_conjElemN_apply,
      slash_Dr_slash_conjElemN hqM' g (inv_mem hγ) (inv_mem hγ0)]
  rw [hinvf, hinvg] at key
  change coeffMap ι₀ ((τ w : KL L q ℓ M') : LaurentSeries L) * qC g' = qC f' at key

  have hw2 : coeffMap ι₀ ((w : KL L q ℓ M') : LaurentSeries L) * qC g' = qC f' := by
    rw [hw, ← ιB, ιB_coeffEmb, map_div₀, ιC_intSeriesC hf', ιC_intSeriesC hg']
    have hne : qC (⇑g') ≠ 0 := by
      rw [← ιC_intSeriesC hg']
      exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0'
    rw [div_mul_cancel₀ _ hne]
  have hne : qC (⇑g') ≠ 0 := by
    rw [← ιC_intSeriesC hg']
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0'
  have heq : coeffMap ι₀ ((τ w : KL L q ℓ M') : LaurentSeries L) = coeffMap ι₀ ((w : KL L q ℓ M') : LaurentSeries L) :=
    mul_right_cancel₀ hne (key.trans hw2.symm)
  exact Subtype.ext (ιB_injective ι₀ heq)

theorem P.of_mem_field {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (q ^ 2 * M') (levelH q M')) :
    P q M' ℓ ξ (coeffEmb L y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH q M')) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact P_algebraMap _
      · exact P.gen hqM' ι₀ hι₀ hy
  | one => rw [map_one]; exact P.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem P.of_mem {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) : P q M' ℓ ξ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact P_algebraMap c
      · exact P.of_mem_field hqM' ι₀ hι₀ hz
  | one => exact P.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Gen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

end Main
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC"

end W1xLE
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

namespace R4GC

open UpperHalfPlane IntermediateField HahnSeries ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

section Borel

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M']

variable (m M') in

abbrev HgpB : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH (m * M') ⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem mem_GammaH_top_iff (A : SL(2, ℤ)) :
    A ∈ CohCarrier.GammaH (m * M') ⊤ ↔ ((A 1 0 : ℤ) : ZMod (m * M')) = 0 := by
  rw [CohCarrier.GammaH_top, Gamma0_mem]

theorem mem_HgpB_iff (A : GL (Fin 2) ℝ) :
    A ∈ HgpB m M' ↔ ∃ ρ : SL(2, ℤ), ρ ∈ Gamma0 M' ∧ (m : ℤ) ∣ ρ 0 1 ∧ conjElemN m ρ = A := by
  constructor
  · rintro ⟨A', hA', rfl⟩
    have h10 : ((A' 1 0 : ℤ) : ZMod (m * M')) = 0 := (mem_GammaH_top_iff A').mp hA'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
    obtain ⟨c, hc⟩ := h10
    have hm : (m : ℤ) ∣ A' 1 0 := ⟨M' * c, by rw [hc]; push_cast; ring⟩
    have hquot : A' 1 0 / (m : ℤ) = M' * c := by
      rw [hc]; push_cast
      rw [show (m : ℤ) * M' * c = m * (M' * c) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
    refine ⟨upSL A' hm, ?_, ?_, conjElemN_upSL A' hm⟩
    · rw [Gamma0_mem]
      show ((A' 1 0 / m : ℤ) : ZMod M') = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hquot]
      exact Dvd.intro _ rfl
    · show (m : ℤ) ∣ (m : ℤ) * A' 0 1
      exact Dvd.intro _ rfl
  · rintro ⟨ρ, hρ, hb, rfl⟩
    rw [conjElemN_eq_downSL' ρ hb]
    refine ⟨downSL ρ hb, (mem_GammaH_top_iff _).mpr ?_, rfl⟩
    show ((((m : ℤ) * ρ 1 0 : ℤ)) : ZMod (m * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hM : (M' : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hρ)
    push_cast
    exact mul_dvd_mul_left (m : ℤ) hM

theorem Γ_le_HgpB : Γ m M' ≤ HgpB m M' := by
  rintro _ ⟨A', hA', rfl⟩
  refine ⟨A', (mem_GammaH_top_iff A').mpr ?_, rfl⟩
  obtain ⟨h10, -⟩ := (mem_GH_iff A').mp hA'
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
  exact dvd_trans ⟨m, by push_cast; ring⟩ h10

theorem isFiniteRelIndex_Γ_HgpB : (Γ m M').IsFiniteRelIndex (HgpB m M') := by
  haveI : NeZero (m * M') := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne M')⟩
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  show ((GH m M').map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
      ((CohCarrier.GammaH (m * M') ⊤).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ≠ 0
  rw [Subgroup.relIndex_map_map_of_injective _ _ (fun γ δ h => coeGL_injective h)]
  haveI : (GH m M').IsFiniteRelIndex (CohCarrier.GammaH (m * M') ⊤) := Subgroup.isFiniteRelIndex_of_finiteIndex
  exact Subgroup.relIndex_ne_zero

end Borel
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

section NormB

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] {ξ : L} (ι₀ : L →+* ℂ)

include hmM'

theorem norm_stepB (w : KL L m M') (hgood : Good hmM' ξ ι₀ (w : LaurentSeries L))
    (hexτ : ∀ ρ : SL(2, ℤ), ρ ∈ Gamma0 M' → (m : ℤ) ∣ ρ 0 1 → ∃ τ : KL L m M' ≃ₐ[L] KL L m M',
      IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') ρ (KL L m M') τ ∧ τ w = w) :
    ∃ (k' : ℤ) (Φ Ψ : ModularForm (HgpB m M') k'), (⇑Ψ : ℍ → ℂ) ≠ 0 ∧ qC Φ ∈ Efield ι₀ ∧ qC Ψ ∈ Efield ι₀ ∧
      ιB ι₀ (w : LaurentSeries L) * qC Ψ = qC Φ := by
  haveI := isFiniteRelIndex_Γ_HgpB (m := m) (M' := M')
  obtain ⟨_, k, F, G, hG, hwe, hE, hτ⟩ := hgood
  have hGq : qC (⇑G) ≠ 0 := fun e => hG ((qC_eq_zero_iff G).mp e)
  have hFG : ∀ h ∈ HgpB m M', ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h) := by
    intro h hh
    obtain ⟨ρ, hρ0, hb, rfl⟩ := (mem_HgpB_iff h).mp hh
    obtain ⟨τ, hτ', hτfix⟩ := hexτ ρ hρ0 hb
    have h1 := hτ w.2 ρ hρ0 τ hτ'
    rw [Subtype.coe_eta, hτfix] at h1
    have h2 : qC (sl hmM' ρ hρ0 F) * qC G = qC F * qC (sl hmM' ρ hρ0 G) := by
      rw [← h1, ← hwe]; ring
    have h3 := mul_eq_mul_of_qC (sl hmM' ρ hρ0 F) G F (sl hmM' ρ hρ0 G) rfl h2
    simpa only [coe_sl] using h3
  obtain ⟨Φ, hΦ⟩ := ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq (Γ m M') (HgpB m M') F G hFG
  set Ψ := ModularForm.norm (HgpB m M') G with hΨdef
  have hGne : (⇑G : ℍ → ℂ) ≠ 0 := fun e => hG (DFunLike.ext' (by rw [e, ModularForm.coe_zero]))
  have hΨne : (⇑Ψ : ℍ → ℂ) ≠ 0 := by
    intro e
    exact ModularForm.norm_ne_zero (HgpB m M') hGne (DFunLike.ext' (by rw [← hΨdef, e, ModularForm.coe_zero]))
  have hΨE : qC (⇑Ψ) ∈ Efield ι₀ := by
    letI := Fintype.ofFinite (HgpB m M' ⧸ (Γ m M').subgroupOf (HgpB m M'))
    have hρc : ∀ c : HgpB m M' ⧸ (Γ m M').subgroupOf (HgpB m M'), ∃ ρ : SL(2, ℤ), ∃ hρ : ρ ∈ Gamma0 M',
        SlashInvariantForm.quotientFunc G c = ⇑(sl hmM' ρ hρ G) := by
      intro c
      have hinv : ((c.out : HgpB m M') : GL (Fin 2) ℝ)⁻¹ ∈ HgpB m M' := inv_mem c.out.2
      obtain ⟨ρ, hρ, -, e⟩ := (mem_HgpB_iff _).mp hinv
      refine ⟨ρ, hρ, ?_⟩
      conv_lhs => rw [← Quotient.out_eq c]
      rw [SlashInvariantForm.quotientFunc_mk, coe_sl, e]
    choose ρ hρ hρe using hρc
    rw [hΨdef, ModularForm.coe_norm]
    have : (∏ c, SlashInvariantForm.quotientFunc G c : ℍ → ℂ) = ∏ c ∈ Finset.univ, (⇑(sl hmM' (ρ c) (hρ c) G) : ℍ → ℂ) :=
      Finset.prod_congr rfl fun c _ => hρe c
    rw [this]
    exact qC_prod_mem ι₀ _ _ fun c _ => (hE (ρ c) (hρ c)).2
  set Φr : ModularForm (Γ m M') _ := restrictForm (Γ_le_HgpB (m := m) (M' := M')) Φ
  set Ψr : ModularForm (Γ m M') _ := restrictForm (Γ_le_HgpB (m := m) (M' := M')) Ψ
  have hq : qC (⇑Φ) * qC G = qC F * qC (⇑Ψ) := by
    rw [show (⇑Φ : ℍ → ℂ) = ⇑Φr from rfl, show (⇑Ψ : ℍ → ℂ) = ⇑Ψr from rfl, ← qC_mul, ← qC_mul]
    exact congrArg qC hΦ
  have hFE : qC (⇑F) ∈ Efield ι₀ := by simpa only [InE, sl_one_eq hmM'] using (hE 1 (one_mem _)).1
  have hGE : qC (⇑G) ∈ Efield ι₀ := by simpa only [InE, sl_one_eq hmM'] using (hE 1 (one_mem _)).2
  refine ⟨_, Φ, Ψ, hΨne, ?_, hΨE, ?_⟩
  · have : qC (⇑Φ) = qC F * qC (⇑Ψ) / qC G := by rw [← hq, mul_div_cancel_right₀ _ hGq]
    rw [this]
    exact div_mem (mul_mem hFE hΨE) hGE
  · apply mul_right_cancel₀ hGq
    rw [mul_assoc, mul_comm (qC (⇑Ψ)), ← mul_assoc, hwe, hq]

omit hmM' in

theorem descentB {k' : ℤ} (Φ Ψ : ModularForm (HgpB m M') k')
    (hΨ : (⇑Ψ : ℍ → ℂ) ≠ 0) (hΦE : qC (⇑Φ) ∈ Efield ι₀) (hΨE : qC (⇑Ψ) ∈ Efield ι₀) :
    ∃ x : LaurentSeries L, x ∈ laurentBaseChange L (xHFunctionField (m * M') ⊤) ∧
      ιB ι₀ x * qC (⇑Ψ) = qC (⇑Φ) := by
  haveI : NeZero (m * M') := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne M')⟩
  have hΨ' : Ψ ≠ 0 := fun e => hΨ (by rw [e, ModularForm.coe_zero])
  exact ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
    (m * M') ⊤ Φ Ψ hΨ' L ι₀ ((inE_iff ι₀ _).mp hΦE) ((inE_iff ι₀ _).mp hΨE)

end NormB
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

section FixB

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = em m)

theorem floorB_le : xHFunctionField (m * M') ⊤ ≤ xHFunctionField (m ^ 2 * M') (levelH m M') := by
  show qExpFunctionFieldC ℚ (CohCarrier.GammaH (m * M') ⊤) ≤ qExpFunctionFieldC ℚ (GH m M')
  refine qExpFunctionFieldC_mono ℚ ?_
  intro A hA
  rw [mem_GammaH_top_iff]
  obtain ⟨h10, -⟩ := (mem_GH_iff A).mp hA
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
  exact dvd_trans ⟨m, by push_cast; ring⟩ h10

variable (L) in
theorem laurentBaseChange_floorB_le :
    laurentBaseChange L (xHFunctionField (m * M') ⊤) ≤ KL L m M' :=
  IntermediateField.adjoin.mono L _ _ (Set.image_mono (fun _ h => floorB_le h))

variable (m M') in

def FixedB (x : LaurentSeries L) : Prop :=
  ∀ (hx : x ∈ KL L m M') (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (m : ℤ) ∣ γ 0 1 →
    ∀ τ : KL L m M' ≃ₐ[L] KL L m M', IsLevelAutAt L m ξ m (m ^ 2 * M') (levelH m M') γ⁻¹ (KL L m M') τ →
      τ ⟨x, hx⟩ = ⟨x, hx⟩

include hmM' hι₀ in

theorem FixedB.gen {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (CohCarrier.GammaH (m * M') ⊤)) :
    FixedB m M' ξ (coeffEmb L y) := by
  intro hx γ hγ hb τ hτ
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  set f' : ModularForm (Γ m M') k := restrictForm (Γ_le_HgpB (m := m) (M' := M')) f
  set g' : ModularForm (Γ m M') k := restrictForm (Γ_le_HgpB (m := m) (M' := M')) g
  have hf' : IsIntegralQExp (⇑f') pf := hf
  have hg' : IsIntegralQExp (⇑g') pg := hg
  have key := hτ k f' g' pf pg hf' hg' hg0 ⟨_, hx⟩ rfl ι₀ hι₀
  have hb' : (m : ℤ) ∣ (γ⁻¹ : SL(2, ℤ)) 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simpa using hb.neg_right
  have hmem : conjElemN m γ⁻¹ ∈ HgpB m M' := (mem_HgpB_iff _).mpr ⟨γ⁻¹, inv_mem hγ, hb', rfl⟩
  have hfs : (⇑f' : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹ = ⇑f' :=
    SlashInvariantFormClass.slash_action_eq f (conjElemN m γ⁻¹) hmem
  have hgs : (⇑g' : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹ = ⇑g' :=
    SlashInvariantFormClass.slash_action_eq g (conjElemN m γ⁻¹) hmem
  rw [hfs, hgs] at key
  change ιB ι₀ ((τ ⟨_, hx⟩ : KL L m M') : LaurentSeries L) * qC (⇑g') = qC (⇑f') at key
  have hgq : qC (⇑g') ≠ 0 := by
    rw [← ιC_intSeriesC hg']; exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0
  have hX : ιB ι₀ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) * qC (⇑g') = qC (⇑f') := by
    rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf', ιC_intSeriesC hg', div_mul_cancel₀ _ hgq]
  apply Subtype.ext
  apply ιB_injective ι₀
  exact mul_right_cancel₀ hgq (key.trans hX.symm)

theorem FixedB.const (c : L) : FixedB m M' ξ (algebraMap L (LaurentSeries L) c) := by
  intro hx γ _ _ τ _
  have e : (⟨algebraMap L (LaurentSeries L) c, hx⟩ : KL L m M') = algebraMap L (KL L m M') c := Subtype.ext rfl
  rw [e, AlgEquiv.commutes]

include hmM' hι₀ in

theorem FixedB.of_mem {x : LaurentSeries L} (hx0 : x ∈ laurentBaseChange L (xHFunctionField (m * M') ⊤)) :
    FixedB m M' ξ x := by
  have hsub : ∀ z, z ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
      (⇑(coeffEmb L) '' (xHFunctionField (m * M') ⊤ : Set (LaurentSeries ℚ)))) → z ∈ KL L m M' := fun z hz =>
    laurentBaseChange_floorB_le L (mem_laurentBaseChange_iff.mpr hz)
  have hsubQ : ∀ z, z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪
      intFormRatiosC ℚ (CohCarrier.GammaH (m * M') ⊤)) → coeffEmb L z ∈ KL L m M' := fun z hz =>
    laurentBaseChange_floorB_le L (coeffEmb_mem_laurentBaseChange L hz)
  rw [mem_laurentBaseChange_iff] at hx0
  induction hx0 using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact FixedB.const ξ c
      · change z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪
          intFormRatiosC ℚ (CohCarrier.GammaH (m * M') ⊤)) at hz
        induction hz using Subfield.closure_induction with
        | mem y hy =>
            rcases hy with ⟨r, rfl⟩ | hy
            · have e0 : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (r : L) := by
                rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
                simp
              rw [e0]; exact FixedB.const ξ _
            · exact FixedB.gen hmM' ξ ι₀ hι₀ hy
        | one =>
            intro hx γ _ _ τ _
            have e : (⟨coeffEmb L 1, hx⟩ : KL L m M') = 1 := Subtype.ext (map_one _)
            rw [e, map_one]
        | add a b ha hb iha ihb =>
            intro hx γ hγ hbb τ hτ
            have e : (⟨coeffEmb L (a + b), hx⟩ : KL L m M') = ⟨_, hsubQ a ha⟩ + ⟨_, hsubQ b hb⟩ := Subtype.ext (map_add _ _ _)
            rw [e, map_add, iha (hsubQ a ha) γ hγ hbb τ hτ, ihb (hsubQ b hb) γ hγ hbb τ hτ]
        | neg a ha iha =>
            intro hx γ hγ hbb τ hτ
            have e : (⟨coeffEmb L (-a), hx⟩ : KL L m M') = -⟨_, hsubQ a ha⟩ := Subtype.ext (map_neg _ _)
            rw [e, map_neg, iha (hsubQ a ha) γ hγ hbb τ hτ]
        | inv a ha iha =>
            intro hx γ hγ hbb τ hτ
            have e : (⟨coeffEmb L a⁻¹, hx⟩ : KL L m M') = (⟨_, hsubQ a ha⟩)⁻¹ := Subtype.ext (by rw [IntermediateField.coe_inv]; exact map_inv₀ (coeffEmb L) a)
            rw [e, map_inv₀, iha (hsubQ a ha) γ hγ hbb τ hτ]
        | mul a b ha hb iha ihb =>
            intro hx γ hγ hbb τ hτ
            have e : (⟨coeffEmb L (a * b), hx⟩ : KL L m M') = ⟨_, hsubQ a ha⟩ * ⟨_, hsubQ b hb⟩ := Subtype.ext (map_mul _ _ _)
            rw [e, map_mul, iha (hsubQ a ha) γ hγ hbb τ hτ, ihb (hsubQ b hb) γ hγ hbb τ hτ]
  | one =>
      intro hx γ _ _ τ _
      have e : (⟨(1 : LaurentSeries L), hx⟩ : KL L m M') = 1 := Subtype.ext rfl
      rw [e, map_one]
  | add a b ha hb iha ihb =>
      intro hx γ hγ hbb τ hτ
      have e : (⟨a + b, hx⟩ : KL L m M') = ⟨a, hsub a ha⟩ + ⟨b, hsub b hb⟩ := rfl
      rw [e, map_add, iha (hsub a ha) γ hγ hbb τ hτ, ihb (hsub b hb) γ hγ hbb τ hτ]
  | neg a ha iha =>
      intro hx γ hγ hbb τ hτ
      have e : (⟨-a, hx⟩ : KL L m M') = -⟨a, hsub a ha⟩ := rfl
      rw [e, map_neg, iha (hsub a ha) γ hγ hbb τ hτ]
  | inv a ha iha =>
      intro hx γ hγ hbb τ hτ
      have e : (⟨a⁻¹, hx⟩ : KL L m M') = (⟨a, hsub a ha⟩)⁻¹ := rfl
      rw [e, map_inv₀, iha (hsub a ha) γ hγ hbb τ hτ]
  | mul a b ha hb iha ihb =>
      intro hx γ hγ hbb τ hτ
      have e : (⟨a * b, hx⟩ : KL L m M') = ⟨a, hsub a ha⟩ * ⟨b, hsub b hb⟩ := rfl
      rw [e, map_mul, iha (hsub a ha) γ hγ hbb τ hτ, ihb (hsub b hb) γ hγ hbb τ hτ]

end FixB
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

end R4GC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.R4GC P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul.W1xLE"

set_option maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))
    :
    ∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 → τ γ w = w) ↔
        ((w : ↥K) : LaurentSeries L) ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) := by
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqM'c : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'
  obtain ⟨ι₀, hι₀⟩ := hι
  subst hK
  have hfloor : ModularCurve.xHFunctionField (q * M') ⊤ =
      ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M')) := by
    show ModularCurve.xHFunctionFieldC ℚ (q * M') ⊤ = _
    unfold ModularCurve.xHFunctionFieldC
    rw [CohCarrier.GammaH_top]
  intro w
  constructor
  · intro hfix
    have hgood := R4GC.Good.of_mem (hmM' := hqM'c) (ξ := ζ) (ι₀ := ι₀) hι₀ w.2
    have hexτ : ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → (q : ℤ) ∣ ρ 0 1 →
        ∃ τ' : R4GC.KL L q M' ≃ₐ[L] R4GC.KL L q M',
          ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ρ (R4GC.KL L q M') τ' ∧
          τ' w = w := fun ρ h0 hb => by
      have hb' : (q : ℤ) ∣ ((ρ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
        simpa using hb.neg_right
      refine ⟨τ ρ⁻¹, ?_, hfix ρ⁻¹ (inv_mem h0) hb'⟩
      have := hτ ρ⁻¹ (inv_mem h0)
      rwa [inv_inv] at this
    obtain ⟨k', Φ, Ψ, hΨ, hΦE, hΨE, hwe⟩ := R4GC.norm_stepB hqM'c ι₀ w hgood hexτ
    obtain ⟨x, hx, hxe⟩ := R4GC.descentB ι₀ Φ Ψ hΨ hΦE hΨE
    rw [hfloor] at hx
    have hΨq : R4GC.qC (⇑Ψ) ≠ 0 := by
      intro e
      have h0 := (R4GC.qC_eq_zero_iff (ModularCurve.restrictForm (R4GC.Γ_le_HgpB (m := q) (M' := M')) Ψ)).mp e
      apply hΨ
      funext z
      exact DFunLike.congr_fun h0 z
    have heq : R4GC.ιB ι₀ x = R4GC.ιB ι₀ (w : LaurentSeries L) :=
      mul_right_cancel₀ hΨq (hxe.trans hwe.symm)
    rw [← R4GC.ιB_injective ι₀ heq]
    exact hx
  · intro hw γ hγ hb
    rw [← hfloor] at hw
    exact R4GC.FixedB.of_mem hqM'c ζ ι₀ hι₀ hw w.2 γ hγ hb (τ γ) (hτ γ hγ)

end S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul (solution)
