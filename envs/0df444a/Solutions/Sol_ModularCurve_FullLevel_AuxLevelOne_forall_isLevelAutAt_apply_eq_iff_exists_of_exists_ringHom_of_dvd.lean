-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f9036c14-49c0-543b-8266-0aac88f9c9e9

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd

open scoped MatrixGroups ModularForm Manifold
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R4H1

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

abbrev GH₀ : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')

abbrev Γ₀ : Subgroup (GL (Fin 2) ℝ) := ((GH₀ m M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Δ : Subgroup SL(2, ℤ) := Gamma m ⊓ Gamma0 M'

variable {m M'}

theorem mem_Δ_iff {δ : SL(2, ℤ)} : δ ∈ Δ m M' ↔ δ ∈ Gamma m ∧ δ ∈ Gamma0 M' := Subgroup.mem_inf

theorem mem_GH₀_iff (A : SL(2, ℤ)) :
    A ∈ GH₀ m M' ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 := by
  rw [GH₀, CohCarrier.mem_GammaH_iff]
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

scoped instance GH₀_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] : (GH₀ m M').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

theorem one_mem_strictPeriods₀ : (1 : ℝ) ∈ (Γ₀ m M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

omit [NeZero m] in
theorem m_dvd_level : (m : ℤ) ∣ ((m ^ 2 * M' : ℕ) : ℤ) := ⟨m * M', by push_cast; ring⟩

theorem m_dvd_lowerLeft_of_mem_GH₀ {δ : SL(2, ℤ)} (hδ : δ ∈ GH₀ m M') : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH₀_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans m_dvd_level h10

theorem upperLeft_of_mem_GH₀ {δ : SL(2, ℤ)} (hδ : δ ∈ GH₀ m M') : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH₀_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact m_dvd_lowerLeft_of_mem_GH₀ hδ
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem upSL_mem_Δ₀ {δ : SL(2, ℤ)} (hδ : δ ∈ GH₀ m M') : upSL δ (m_dvd_lowerLeft_of_mem_GH₀ hδ) ∈ Δ m M' := by
  obtain ⟨h10, h11⟩ := (mem_GH₀_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  have hquot : δ 1 0 / (m : ℤ) = m * (M' * c) := by
    rw [hc]; push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  refine mem_Δ_iff.mpr ⟨?_, ?_⟩
  · rw [Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ((δ 0 0 : ℤ) : ZMod m) = 1
      exact upperLeft_of_mem_GH₀ hδ
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

theorem downSL_mem₀ {δ : SL(2, ℤ)} (hδ : δ ∈ Δ m M') :
    downSL (m := m) δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1) ∈ GH₀ m M' := by
  obtain ⟨-, -, h10, h11⟩ := Gamma_mem.mp (mem_Δ_iff.mp hδ).1
  rw [mem_GH₀_iff]
  refine ⟨?_, h11⟩
  show ((((m : ℤ) * δ 1 0 : ℤ)) : ZMod (m ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (m : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hM : (M' : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (mem_Δ_iff.mp hδ).2)
  have hcop : IsCoprime (m : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hmM'
  obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
  exact ⟨c, by rw [hc]; push_cast; ring⟩

theorem mem_Γ₀_iff_exists (A : GL (Fin 2) ℝ) : A ∈ Γ₀ m M' ↔ ∃ δ ∈ Δ m M', conjElemN m δ = A := by
  constructor
  · rintro ⟨A', hA', rfl⟩
    exact ⟨upSL A' (m_dvd_lowerLeft_of_mem_GH₀ hA'), upSL_mem_Δ₀ hA', conjElemN_upSL _ _⟩
  · rintro ⟨δ, hδ, rfl⟩
    rw [conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1)]
    exact ⟨_, downSL_mem₀ hmM' hδ, rfl⟩

theorem conj_mem_Γ₀ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {A : GL (Fin 2) ℝ} (hA : A ∈ Γ₀ m M') :
    conjElemN m γ * A * (conjElemN m γ)⁻¹ ∈ Γ₀ m M' := by
  obtain ⟨δ, hδ, rfl⟩ := (mem_Γ₀_iff_exists hmM' A).mp hA
  rw [← conjElemN_inv, ← conjElemN_mul, ← conjElemN_mul, mem_Γ₀_iff_exists hmM']
  refine ⟨γ * δ * γ⁻¹, mem_Δ_iff.mpr ⟨?_, ?_⟩, rfl⟩
  · exact (Gamma_normal m).conj_mem δ (mem_Δ_iff.mp hδ).1 γ
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ (mem_Δ_iff.mp hδ).2) (Subgroup.inv_mem _ hγ)

theorem le_conj₀ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ₀ m M' ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ₀ m M' := by
  intro A hA
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  exact conj_mem_Γ₀ hmM' hγ hA

end Group

end R4H1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

structure R4H1.Hyp (m M' ℓg : ℕ) (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Prop where
  cop : Nat.Coprime m M'
  dvd : ℓg ∣ M'
  eq : H₁ = ModularCurve.FullLevel.levelH m M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left dvd (m ^ 2))).ker

namespace R4H1

section GroupH1

variable (m : ℕ) [NeZero m] (M' : ℕ)

abbrev GH (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') H₁

abbrev Γ (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GH m M' H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {m M'} {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}

scoped instance GH_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) :
    (GH m M' H₁).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M' H₁).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

theorem det2 (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

theorem mul_apply_11 (A B : SL(2, ℤ)) : (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply_10 (A B : SL(2, ℤ)) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_apply_01 (A : SL(2, ℤ)) : (A⁻¹) 0 1 = -A 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; rfl

theorem inv_apply_11 (A : SL(2, ℤ)) : (A⁻¹) 1 1 = A 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; rfl

variable (hH : Hyp m M' ℓg H₁)
include hH

omit [NeZero m] in
theorem ℓg_dvd_level : ℓg ∣ m ^ 2 * M' := Dvd.dvd.mul_left hH.dvd (m ^ 2)

omit [NeZero m] in
theorem H₁_le_levelH : H₁ ≤ levelH m M' := by rw [hH.eq]; exact inf_le_left

omit [NeZero m] in
theorem GH_le_GH₀ : GH m M' H₁ ≤ GH₀ m M' := GammaH_mono (H₁_le_levelH hH)

omit [NeZero m] in
theorem Γ_le_Γ₀ : Γ m M' H₁ ≤ Γ₀ m M' := Subgroup.map_mono (GH_le_GH₀ hH)

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' H₁ ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 ∧
      ((A 1 1 : ℤ) : ZMod ℓg) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff, hH.eq]
  constructor
  · rintro ⟨hA, hHL⟩
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_levelH_iff] at hHL
    obtain ⟨hH', hL⟩ := hHL
    refine ⟨Gamma0_mem.mp hA, ?_, ?_⟩
    · have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH'
      simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
    · have := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) hL
      simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11, h11'⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_levelH_iff]
    refine ⟨?_, ?_⟩
    · ext
      simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]
    · ext
      simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11']

theorem m_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) : (m : ℤ) ∣ δ 1 0 :=
  m_dvd_lowerLeft_of_mem_GH₀ (GH_le_GH₀ hH hδ)

theorem upSL_mem_Δ {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) :
    upSL δ (m_dvd_lowerLeft_of_mem_GH hH hδ) ∈ Δ m M' :=
  upSL_mem_Δ₀ (GH_le_GH₀ hH hδ)

theorem lowerRight_ℓ_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) : ((δ 1 1 : ℤ) : ZMod ℓg) = 1 :=
  ((mem_GH_iff hH δ).mp hδ).2.2

theorem downSL_mem {δ : SL(2, ℤ)} (hδ : δ ∈ Δ m M') (hℓ : ((δ 1 1 : ℤ) : ZMod ℓg) = 1) :
    downSL (m := m) δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1) ∈ GH m M' H₁ := by
  have h0 := downSL_mem₀ hH.cop hδ
  obtain ⟨h10, h11⟩ := (mem_GH₀_iff _).mp h0
  exact (mem_GH_iff hH _).mpr ⟨h10, h11, hℓ⟩

theorem mem_Γ_iff_exists (A : GL (Fin 2) ℝ) :
    A ∈ Γ m M' H₁ ↔ ∃ δ ∈ Δ m M', ((δ 1 1 : ℤ) : ZMod ℓg) = 1 ∧ conjElemN m δ = A := by
  constructor
  · rintro ⟨A', hA', rfl⟩
    exact ⟨upSL A' (m_dvd_lowerLeft_of_mem_GH hH hA'), upSL_mem_Δ hH hA',
      (by show ((A' 1 1 : ℤ) : ZMod ℓg) = 1; exact lowerRight_ℓ_of_mem_GH hH hA'), conjElemN_upSL _ _⟩
  · rintro ⟨δ, hδ, hℓ, rfl⟩
    rw [conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ).1)]
    exact ⟨_, downSL_mem hH hδ hℓ, rfl⟩

theorem lowerLeft_mod_ℓ_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : ((γ 1 0 : ℤ) : ZMod ℓg) = 0 := by
  have := Gamma0_mem.mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hH.dvd) this

theorem diag_mod_ℓ_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    ((γ 0 0 : ℤ) : ZMod ℓg) * ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
  have h10 := lowerLeft_mod_ℓ_of_mem_Gamma0 hH hγ
  have := congrArg (fun z : ℤ => (z : ZMod ℓg)) (det2 γ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h10, mul_zero, sub_zero] at this
  exact this

theorem lowerRight_conj {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M')
    (hℓ : ((δ 1 1 : ℤ) : ZMod ℓg) = 1) : (((γ * δ * γ⁻¹) 1 1 : ℤ) : ZMod ℓg) = 1 := by
  have g10 := lowerLeft_mod_ℓ_of_mem_Gamma0 hH hγ
  have d10 := lowerLeft_mod_ℓ_of_mem_Gamma0 hH hδ
  have gdet := diag_mod_ℓ_of_mem_Gamma0 hH hγ
  have e1 : ((γ * δ) 1 0 : ℤ) = γ 1 0 * δ 0 0 + γ 1 1 * δ 1 0 := mul_apply_10 γ δ
  have e2 : ((γ * δ) 1 1 : ℤ) = γ 1 0 * δ 0 1 + γ 1 1 * δ 1 1 := mul_apply_11 γ δ
  have e3 : ((γ * δ * γ⁻¹) 1 1 : ℤ) = (γ * δ) 1 0 * (γ⁻¹) 0 1 + (γ * δ) 1 1 * (γ⁻¹) 1 1 := mul_apply_11 _ _
  rw [e3, e1, e2, inv_apply_01, inv_apply_11]
  push_cast
  rw [g10, d10, hℓ]
  linear_combination gdet

theorem conj_mem_Γ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {A : GL (Fin 2) ℝ} (hA : A ∈ Γ m M' H₁) :
    conjElemN m γ * A * (conjElemN m γ)⁻¹ ∈ Γ m M' H₁ := by
  obtain ⟨δ, hδ, hℓ, rfl⟩ := (mem_Γ_iff_exists hH A).mp hA
  rw [← conjElemN_inv, ← conjElemN_mul, ← conjElemN_mul, mem_Γ_iff_exists hH]
  refine ⟨γ * δ * γ⁻¹, mem_Δ_iff.mpr ⟨?_, ?_⟩, lowerRight_conj hH hγ (mem_Δ_iff.mp hδ).2 hℓ, rfl⟩
  · exact (Gamma_normal m).conj_mem δ (mem_Δ_iff.mp hδ).1 γ
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ (mem_Δ_iff.mp hδ).2) (Subgroup.inv_mem _ hγ)

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ m M' H₁ ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' H₁ := by
  intro A hA
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  exact conj_mem_Γ hH hγ hA

end GroupH1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

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

theorem Γ₀_le_Hgp : Γ₀ m M' ≤ Hgp n m M' := fun A hA => by
  rw [mem_Hgp_iff]
  obtain ⟨δ, hδ, e⟩ := (mem_Γ₀_iff_exists hmM' A).mp hA
  exact ⟨δ, Δ_le_of_dvd hnm hδ, e⟩

theorem isFiniteRelIndex_Γ₀_Hgp [NeZero M'] : (Γ₀ m M').IsFiniteRelIndex (Hgp n m M') := by
  have hle : (Gamma (m ^ 2 * M')).map (shp m) ≤ Γ₀ m M' := by
    rintro _ ⟨δ, hδ, rfl⟩
    have hδ' : δ ∈ Δ m M' := by
      refine mem_Δ_iff.mpr ⟨Gamma_le_of_dvd ⟨m * M', by ring⟩ hδ, ?_⟩
      rw [Gamma0_mem]
      have h3 := (Gamma_mem.mp hδ).2.2.1
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢
      exact dvd_trans ⟨m ^ 2, by push_cast; ring⟩ h3
    rw [shp_apply, conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ').1)]
    exact ⟨_, downSL_mem₀ hmM' hδ', rfl⟩
  haveI : NeZero (m ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (NeZero.ne m)) (NeZero.ne M')⟩
  haveI : ((Gamma (m ^ 2 * M')).map (shp m)).IsFiniteRelIndex (Hgp n m M') := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Hgp,
      Subgroup.relIndex_map_map_of_injective _ _ (shp_injective m)]
    haveI : (Gamma (m ^ 2 * M')).IsFiniteRelIndex (Δ n M') := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  exact Subgroup.isFiniteRelIndex_of_le_left (Hgp n m M') hle

omit hmM' in

theorem Γ_le_Hgp {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ} (hH : Hyp m M' ℓg H₁) :
    Γ m M' H₁ ≤ Hgp n m M' :=
  le_trans (Γ_le_Γ₀ hH) (Γ₀_le_Hgp hH.cop hnm)

omit hmM' in

theorem isFiniteRelIndex_Γ_Hgp [NeZero M'] {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ} (hH : Hyp m M' ℓg H₁) :
    (Γ m M' H₁).IsFiniteRelIndex (Hgp n m M') := by
  have hle : (Gamma (m ^ 2 * M')).map (shp m) ≤ Γ m M' H₁ := by
    rintro _ ⟨δ, hδ, rfl⟩
    have hδ' : δ ∈ Δ m M' := by
      refine mem_Δ_iff.mpr ⟨Gamma_le_of_dvd ⟨m * M', by ring⟩ hδ, ?_⟩
      rw [Gamma0_mem]
      have h3 := (Gamma_mem.mp hδ).2.2.1
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢
      exact dvd_trans ⟨m ^ 2, by push_cast; ring⟩ h3
    have hℓ : ((δ 1 1 : ℤ) : ZMod ℓg) = 1 := by
      have h4 := (Gamma_mem.mp hδ).2.2.2
      have := congrArg (ZMod.castHom (ℓg_dvd_level hH) (ZMod ℓg)) h4
      rwa [map_intCast, map_one] at this
    rw [shp_apply, conjElemN_eq_downSL' δ (m_dvd_01_of_mem_Gamma (mem_Δ_iff.mp hδ').1)]
    exact ⟨_, downSL_mem hH hδ' hℓ, rfl⟩
  haveI : NeZero (m ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (NeZero.ne m)) (NeZero.ne M')⟩
  haveI : ((Gamma (m ^ 2 * M')).map (shp m)).IsFiniteRelIndex (Hgp n m M') := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Hgp,
      Subgroup.relIndex_map_map_of_injective _ _ (shp_injective m)]
    haveI : (Gamma (m ^ 2 * M')).IsFiniteRelIndex (Δ n M') := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  exact Subgroup.isFiniteRelIndex_of_le_left (Hgp n m M') hle

end Frame
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

section Analytic

variable {m : ℕ} [NeZero m] {M' : ℕ} {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}

section Slash

variable (hmM' : Hyp m M' ℓg H₁)
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) : ModularForm (Γ m M' H₁) k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_mul_coe {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ m M' H₁) k₁) (g : ModularForm (Γ m M' H₁) k₂) :
    ⇑(sl hmM' γ hγ (f.mul g)) = ⇑(sl hmM' γ hγ f) * ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElemN_val, abs_one, one_smul]

theorem sl_add_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ (f + g)) = ⇑(sl hmM' γ hγ f) + ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash]

theorem sl_neg_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ (-f)) = -⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

theorem sl_zero_coe {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ⇑(sl hmM' γ hγ (0 : ModularForm (Γ m M' H₁) k)) = 0 := by
  simp only [coe_sl, ModularForm.coe_zero, SlashAction.zero_slash]

theorem sl_one_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ⇑(sl hmM' γ hγ (1 : ModularForm (Γ m M' H₁) 0)) = 1 := by
  funext τ
  simp only [coe_sl, ModularForm.one_coe_eq_one, ModularForm.slash_def, Pi.one_apply, σ_conjElemN_apply,
    det_conjElemN_val]
  simp

theorem sl_const_coe (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    ⇑(sl hmM' γ hγ (ModularForm.const c : ModularForm (Γ m M' H₁) 0)) = ⇑(ModularForm.const c : ModularForm (Γ m M' H₁) 0) := by
  funext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElemN_apply,
    det_conjElemN_val]
  simp

theorem sl_sl_inv {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    sl hmM' γ⁻¹ (Subgroup.inv_mem _ hγ) (sl hmM' γ hγ f) = f := by
  ext τ
  simp only [coe_sl]
  rw [← SlashAction.slash_mul, ← conjElemN_mul, mul_inv_cancel, ← shp_apply, map_one, SlashAction.slash_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M' H₁) k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_sl_inv hmM' γ hγ f, h]
  ext τ
  simp [coe_sl]

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M' H₁) k₁) (g : ModularForm (Γ m M' H₁) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g]

theorem qC_add {k : ℤ} (f g : ModularForm (Γ m M' H₁) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ m M' H₁) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ m M' H₁) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ m M' H₁) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) = c • ((1 : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) := by
  funext z
  simp [ModularForm.one_coe_eq_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

theorem qC_coeff_neg (F : ℍ → ℂ) {n : ℤ} (hn : n < 0) : (qC F).coeff n = 0 :=
  ModularCurve.ofPowerSeries_coeff_of_neg _ hn

theorem qC_coeff_nat (F : ℍ → ℂ) (n : ℕ) : (qC F).coeff (n : ℤ) = (qExpansion 1 F).coeff n :=
  ofPowerSeries_apply_coeff _ _

theorem qC_sum_smul {k : ℤ} (s : Finset ℕ) (c : ℕ → ℂ) (h : ℕ → ModularForm (Γ m M' H₁) k) :
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

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M' H₁) k₁) (f₂ : ModularForm (Γ m M' H₁) k₂)
    (f₃ : ModularForm (Γ m M' H₁) k₃) (f₄ : ModularForm (Γ m M' H₁) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ m M' H₁) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
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

theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ m M' H₁) k₁} {g₂ : ModularForm (Γ m M' H₁) k₂}
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

theorem inE_sl_of_rat [NeZero M'] (hmM' : Hyp m M' ℓg H₁) {ξ : L} (hι₀ : ι₀ ξ = em m) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ m M' H₁) k) (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ))
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M') : InE ι₀ (sl hmM' ρ hρ f) := by
  obtain ⟨h, hrat, hslash⟩ :=
    ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker m M' hmM'.cop
      ℓg hmM'.dvd H₁ hmM'.eq hk f hf ρ hρ
  have hcomm : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] * (ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
      = (ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] := by
    have : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this, Matrix.one_mul, Matrix.mul_one]
  have key := hslash 1 ρ (Nat.coprime_one_left m) hρ rfl hcomm
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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

section Good

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ} (hmM' : Hyp m M' ℓg H₁)
variable {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = em m)

abbrev KL (L : Type) [Field L] [CharZero L] (m : ℕ) (M' : ℕ) (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) :
    IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') H₁)

def Good (x : LaurentSeries L) : Prop :=
  x ∈ KL L m M' H₁ ∧
  ∃ (k : ℤ) (F G : ModularForm (Γ m M' H₁) k), G ≠ 0 ∧ ιB ι₀ x * qC G = qC F ∧
    (∀ (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M'), InE ι₀ (sl hmM' ρ hρ F) ∧ InE ι₀ (sl hmM' ρ hρ G)) ∧
    (∀ (hx : x ∈ KL L m M' H₁) (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M') (τ : KL L m M' H₁ ≃ₐ[L] KL L m M' H₁),
      IsLevelAutAt L m ξ m (m ^ 2 * M') H₁ ρ (KL L m M' H₁) τ →
        ιB ι₀ ((τ ⟨x, hx⟩ : KL L m M' H₁) : LaurentSeries L) * qC (sl hmM' ρ hρ G) = qC (sl hmM' ρ hρ F))

variable {hmM' ξ ι₀}

theorem Good.mem {x : LaurentSeries L} (h : Good hmM' ξ ι₀ x) : x ∈ KL L m M' H₁ := h.1

theorem one_form_ne_zero : (1 : ModularForm (Γ m M' H₁) 0) ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Γ m M' H₁) 0 => qC (⇑f)) h
  simp only [ModularForm.one_coe_eq_one, qC_one, ModularForm.coe_zero, qC_zero] at this
  exact one_ne_zero this

theorem Good.const (c : L) : Good hmM' ξ ι₀ (algebraMap L (LaurentSeries L) c) := by
  have hmem : algebraMap L (LaurentSeries L) c ∈ KL L m M' H₁ := IntermediateField.algebraMap_mem _ c
  refine ⟨hmem, 0, ModularForm.const (ι₀ c), 1, one_form_ne_zero, ?_, ?_, ?_⟩
  · rw [ιB_algebraMap, ModularForm.one_coe_eq_one, qC_one, mul_one, qC_const]
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · rw [InE, sl_const_coe, qC_const]; exact C_mem_Efield ι₀ c
    · rw [InE, sl_one_coe, qC_one]; exact one_mem _
  · intro hx ρ hρ τ _
    have e : (⟨algebraMap L (LaurentSeries L) c, hx⟩ : KL L m M' H₁) = algebraMap L (KL L m M' H₁) c := Subtype.ext rfl
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
    have e : (⟨x + y, hxy⟩ : KL L m M' H₁) = ⟨x, hxm⟩ + ⟨y, hym⟩ := Subtype.ext rfl
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
    have e : (⟨-x, hx'⟩ : KL L m M' H₁) = -⟨x, hxm⟩ := Subtype.ext rfl
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
    have e : (⟨x * y, hxy⟩ : KL L m M' H₁) = ⟨x, hxm⟩ * ⟨y, hym⟩ := Subtype.ext rfl
    rw [e, map_mul, IntermediateField.coe_mul, map_mul, sl_mul_coe, sl_mul_coe, qC_mul, qC_mul]
    have h1 := hxτ hxm ρ hρ τ hτ
    have h2 := hyτ hym ρ hρ τ hτ
    linear_combination ιB ι₀ ((τ ⟨y, hym⟩ : KL L m M' H₁) : LaurentSeries L) * qC (sl hmM' ρ hρ G₂) * h1 +
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
    have e : (⟨x⁻¹, hx'⟩ : KL L m M' H₁) = (⟨x, hxm⟩ : KL L m M' H₁)⁻¹ := Subtype.ext rfl
    have h1 := hxτ hxm ρ hρ τ hτ
    have hFq : qC (sl hmM' ρ hρ F) ≠ 0 := fun e => sl_ne_zero hmM' ρ hρ hF ((qC_eq_zero_iff _).mp e)
    have hτx : ιB ι₀ ((τ ⟨x, hxm⟩ : KL L m M' H₁) : LaurentSeries L) ≠ 0 := by
      intro e0; rw [e0, zero_mul] at h1; exact hFq h1.symm
    rw [e, map_inv₀, IntermediateField.coe_inv, map_inv₀, ← h1, inv_mul_cancel_left₀ hτx]

theorem rat_coeff_mul {k : ℤ} (f g : ModularForm (Γ m M' H₁) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(f.mul g))).coeff n = (r : ℂ) := by
  rw [ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g, ← hf, ← hg,
    ← map_mul, PowerSeries.coeff_map]
  exact ⟨((PowerSeries.coeff n (pf * pg) : ℤ) : ℚ), by simp⟩

theorem Good.gen (hι₀ : ι₀ ξ = em m) {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH m M' H₁)) :
    Good hmM' ξ ι₀ (coeffEmb L y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  have hmem : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ KL L m M' H₁ :=
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
    change ιB ι₀ ((τ ⟨_, hx⟩ : KL L m M' H₁) : LaurentSeries L) * qC (sl hmM' ρ hρ g) = qC (sl hmM' ρ hρ f) at key
    rw [sl_mul_coe, sl_mul_coe, qC_mul, qC_mul, ← key]
    ring

theorem Good.of_mem_field (hι₀ : ι₀ ξ = em m) {y : LaurentSeries ℚ}
    (hy : y ∈ xHFunctionField (m ^ 2 * M') H₁) : Good hmM' ξ ι₀ (coeffEmb L y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M' H₁)) at hy
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

theorem Good.of_mem (hι₀ : ι₀ ξ = em m) {x : LaurentSeries L} (hx : x ∈ KL L m M' H₁) : Good hmM' ξ ι₀ x := by
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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

section Norm

variable {n m : ℕ} [NeZero n] [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}
  (hmM' : Hyp m M' ℓg H₁) (hnm : n ∣ m)
variable {L : Type} [Field L] [CharZero L] {ξ : L} (ι₀ : L →+* ℂ)

theorem sl_one_eq {k : ℤ} (F : ModularForm (Γ m M' H₁) k) : sl hmM' 1 (one_mem _) F = F := by
  ext τ
  simp only [coe_sl, ← shp_apply, map_one, SlashAction.slash_one]

theorem qC_prod_mem {ι : Type} (s : Finset ι) {k : ℤ} (F : ι → ModularForm (Γ m M' H₁) k)
    (hF : ∀ i ∈ s, InE ι₀ (F i)) : qC (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) ∈ Efield ι₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, qC_one]; exact one_mem _
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, ← ModularForm.coe_prodEqualWeights (s := t) F, qC_mul]
      rw [ModularForm.coe_prodEqualWeights]
      exact mul_mem (hF a (Finset.mem_insert_self a t)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

include hmM' hnm

theorem norm_step (w : KL L m M' H₁) (hgood : Good hmM' ξ ι₀ (w : LaurentSeries L))
    (hexτ : ∀ ρ ∈ Δ n M', ∃ τ : KL L m M' H₁ ≃ₐ[L] KL L m M' H₁,
      IsLevelAutAt L m ξ m (m ^ 2 * M') H₁ ρ (KL L m M' H₁) τ)
    (hfix : ∀ ρ ∈ Δ n M', ∀ τ : KL L m M' H₁ ≃ₐ[L] KL L m M' H₁,
      IsLevelAutAt L m ξ m (m ^ 2 * M') H₁ ρ (KL L m M' H₁) τ → τ w = w) :
    ∃ (k' : ℤ) (Φ Ψ : ModularForm (Hgp n m M') k'), (⇑Ψ : ℍ → ℂ) ≠ 0 ∧ qC Φ ∈ Efield ι₀ ∧ qC Ψ ∈ Efield ι₀ ∧
      ιB ι₀ (w : LaurentSeries L) * qC Ψ = qC Φ := by
  haveI := isFiniteRelIndex_Γ_Hgp (n := n) hnm hmM'
  obtain ⟨_, k, F, G, hG, hwe, hE, hτ⟩ := hgood
  have hGq : qC (⇑G) ≠ 0 := fun e => hG ((qC_eq_zero_iff G).mp e)

  have hFG : ∀ h ∈ Hgp n m M', ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) = (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h) := by
    intro h hh
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Hgp_iff h).mp hh
    have hρ0 : ρ ∈ Gamma0 M' := (mem_Δ_iff.mp hρ).2
    obtain ⟨τ, hτ'⟩ := hexτ ρ hρ
    have h1 := hτ w.2 ρ hρ0 τ hτ'
    rw [Subtype.coe_eta, hfix ρ hρ τ hτ'] at h1

    have h2 : qC (sl hmM' ρ hρ0 F) * qC G = qC F * qC (sl hmM' ρ hρ0 G) := by
      rw [← h1, ← hwe]; ring
    have h3 := mul_eq_mul_of_qC (sl hmM' ρ hρ0 F) G F (sl hmM' ρ hρ0 G) rfl h2
    simpa only [coe_sl] using h3
  obtain ⟨Φ, hΦ⟩ := ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq (Γ m M' H₁) (Hgp n m M') F G hFG
  set Ψ := ModularForm.norm (Hgp n m M') G with hΨdef
  have hGne : (⇑G : ℍ → ℂ) ≠ 0 := fun e => hG (DFunLike.ext' (by rw [e, ModularForm.coe_zero]))
  have hΨne : (⇑Ψ : ℍ → ℂ) ≠ 0 := by
    intro e
    exact ModularForm.norm_ne_zero (Hgp n m M') hGne (DFunLike.ext' (by rw [← hΨdef, e, ModularForm.coe_zero]))

  have hΨE : qC (⇑Ψ) ∈ Efield ι₀ := by
    letI := Fintype.ofFinite (Hgp n m M' ⧸ (Γ m M' H₁).subgroupOf (Hgp n m M'))
    have hρc : ∀ c : Hgp n m M' ⧸ (Γ m M' H₁).subgroupOf (Hgp n m M'), ∃ ρ : SL(2, ℤ), ∃ hρ : ρ ∈ Gamma0 M',
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

  set Φr : ModularForm (Γ m M' H₁) _ := restrictForm (Γ_le_Hgp hnm hmM') Φ
  set Ψr : ModularForm (Γ m M' H₁) _ := restrictForm (Γ_le_Hgp hnm hmM') Ψ
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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

section Descent

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M']
variable {L : Type} [Field L] [CharZero L] (ι₀ : L →+* ℂ)

theorem descent_step (hmM' : Nat.Coprime m M') {k' : ℤ} (Φ Ψ : ModularForm (Hgp m m M') k')
    (hΨ : (⇑Ψ : ℍ → ℂ) ≠ 0) (hΦE : qC (⇑Φ) ∈ Efield ι₀) (hΨE : qC (⇑Ψ) ∈ Efield ι₀) :
    ∃ x : LaurentSeries L, x ∈ laurentBaseChange L (xHFunctionField (m ^ 2 * M') (levelH m M')) ∧
      ιB ι₀ x * qC (⇑Ψ) = qC (⇑Φ) := by
  set Φ₁ : ModularForm (Γ₀ m M') k' := restrictForm (Γ₀_le_Hgp hmM' dvd_rfl) Φ
  set Ψ₁ : ModularForm (Γ₀ m M') k' := restrictForm (Γ₀_le_Hgp hmM' dvd_rfl) Ψ
  have hΨ₁ : Ψ₁ ≠ 0 := by
    intro e
    apply hΨ
    have : (⇑Ψ₁ : ℍ → ℂ) = 0 := by rw [e, ModularForm.coe_zero]
    exact this
  have hΦ₁ := (inE_iff ι₀ (⇑Φ₁ : ℍ → ℂ)).mp hΦE
  have hΨ₁' := (inE_iff ι₀ (⇑Ψ₁ : ℍ → ℂ)).mp hΨE
  obtain ⟨x, hx, hxe⟩ :=
    ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range (m ^ 2 * M')
      (levelH m M') Φ₁ Ψ₁ hΨ₁ L ι₀ hΦ₁ hΨ₁'
  exact ⟨x, hx, hxe⟩

end Descent
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

section Elementary

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}
variable {L : Type} [Field L] [CharZero L]

variable (m M' H₁) in

def Fixed (ξ : L) (x : LaurentSeries L) : Prop :=
  ∃ hx : x ∈ KL L m M' H₁, ∀ γ ∈ Δ m M', ∀ τ : KL L m M' H₁ ≃ₐ[L] KL L m M' H₁,
    IsLevelAutAt L m ξ m (m ^ 2 * M') H₁ γ⁻¹ (KL L m M' H₁) τ → ((τ ⟨x, hx⟩ : KL L m M' H₁) : LaurentSeries L) = x

variable {ξ : L}

theorem Fixed.const (c : L) : Fixed m M' H₁ ξ (algebraMap L (LaurentSeries L) c) := by
  refine ⟨IntermediateField.algebraMap_mem _ c, fun γ _ τ _ => ?_⟩
  have e : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ : KL L m M' H₁) =
      algebraMap L (KL L m M' H₁) c := Subtype.ext rfl
  rw [e, AlgEquiv.commutes]
  rfl

theorem Fixed.add {x y : LaurentSeries L} (hx : Fixed m M' H₁ ξ x) (hy : Fixed m M' H₁ ξ y) :
    Fixed m M' H₁ ξ (x + y) := by
  obtain ⟨hxm, hxf⟩ := hx
  obtain ⟨hym, hyf⟩ := hy
  refine ⟨add_mem hxm hym, fun γ hγ τ hτ => ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : KL L m M' H₁) = ⟨x, hxm⟩ + ⟨y, hym⟩ := Subtype.ext rfl
  rw [e, map_add, IntermediateField.coe_add, hxf γ hγ τ hτ, hyf γ hγ τ hτ]

theorem Fixed.neg {x : LaurentSeries L} (hx : Fixed m M' H₁ ξ x) : Fixed m M' H₁ ξ (-x) := by
  obtain ⟨hxm, hxf⟩ := hx
  refine ⟨neg_mem hxm, fun γ hγ τ hτ => ?_⟩
  have e : (⟨-x, neg_mem hxm⟩ : KL L m M' H₁) = -⟨x, hxm⟩ := Subtype.ext rfl
  rw [e, map_neg, IntermediateField.coe_neg, hxf γ hγ τ hτ]

theorem Fixed.mul {x y : LaurentSeries L} (hx : Fixed m M' H₁ ξ x) (hy : Fixed m M' H₁ ξ y) :
    Fixed m M' H₁ ξ (x * y) := by
  obtain ⟨hxm, hxf⟩ := hx
  obtain ⟨hym, hyf⟩ := hy
  refine ⟨mul_mem hxm hym, fun γ hγ τ hτ => ?_⟩
  have e : (⟨x * y, mul_mem hxm hym⟩ : KL L m M' H₁) = ⟨x, hxm⟩ * ⟨y, hym⟩ := Subtype.ext rfl
  rw [e, map_mul, IntermediateField.coe_mul, hxf γ hγ τ hτ, hyf γ hγ τ hτ]

theorem Fixed.inv {x : LaurentSeries L} (hx : Fixed m M' H₁ ξ x) : Fixed m M' H₁ ξ x⁻¹ := by
  obtain ⟨hxm, hxf⟩ := hx
  refine ⟨inv_mem hxm, fun γ hγ τ hτ => ?_⟩
  have e : (⟨x⁻¹, inv_mem hxm⟩ : KL L m M' H₁) = (⟨x, hxm⟩ : KL L m M' H₁)⁻¹ := Subtype.ext rfl
  rw [e, map_inv₀, IntermediateField.coe_inv, hxf γ hγ τ hτ]

theorem Fixed.one : Fixed m M' H₁ ξ (1 : LaurentSeries L) := by
  have := Fixed.const (m := m) (M' := M') (H₁ := H₁) (ξ := ξ) (1 : L)
  rwa [map_one] at this

variable (hmM' : Hyp m M' ℓg H₁) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = em m)
include hmM' hι₀

theorem Fixed.gen {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH₀ m M')) :
    Fixed m M' H₁ ξ (coeffEmb L y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy

  set f₁ : ModularForm (Γ m M' H₁) k := restrictForm (Γ_le_Γ₀ hmM') f with hf₁
  set g₁ : ModularForm (Γ m M' H₁) k := restrictForm (Γ_le_Γ₀ hmM') g with hg₁
  have hf' : IsIntegralQExp (⇑f₁) pf := hf
  have hg' : IsIntegralQExp (⇑g₁) pg := hg
  have hmem : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ KL L m M' H₁ :=
    coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f₁ g₁ hf' hg' hg0)
  refine ⟨hmem, fun γ hγ τ hτ => ?_⟩
  have hgq : qC (⇑g) ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

  have hγ' : γ⁻¹ ∈ Δ m M' := Subgroup.inv_mem _ hγ
  have hmemΓ : conjElemN m γ⁻¹ ∈ Γ₀ m M' := (mem_Γ₀_iff_exists hmM'.cop _).mpr ⟨γ⁻¹, hγ', rfl⟩
  have hfix_f : ((⇑f : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹) = ⇑f := SlashInvariantForm.slash_action_eqn f _ hmemΓ
  have hfix_g : ((⇑g : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹) = ⇑g := SlashInvariantForm.slash_action_eqn g _ hmemΓ
  have hw : ιB ι₀ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) * qC (⇑g) = qC (⇑f) := by
    rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
    field_simp
  have key := hτ k f₁ g₁ pf pg hf' hg' hg0 ⟨_, hmem⟩ rfl ι₀ hι₀
  change ιB ι₀ ((τ ⟨_, hmem⟩ : KL L m M' H₁) : LaurentSeries L) * qC ((⇑g : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹) =
    qC ((⇑f : ℍ → ℂ) ∣[k] conjElemN m γ⁻¹) at key
  rw [hfix_f, hfix_g] at key
  exact ιB_injective ι₀ (mul_right_cancel₀ hgq (key.trans hw.symm))

theorem Fixed.of_mem_field {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (m ^ 2 * M') (levelH m M')) :
    Fixed m M' H₁ ξ (coeffEmb L y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH₀ m M')) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact Fixed.const _
      · exact Fixed.gen hmM' ι₀ hι₀ hy
  | one => rw [map_one]; exact Fixed.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem Fixed.of_mem {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L (xHFunctionField (m ^ 2 * M') (levelH m M'))) :
    Fixed m M' H₁ ξ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact Fixed.const c
      · exact Fixed.of_mem_field hmM' ι₀ hι₀ hz
  | one => exact Fixed.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Elementary
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

end R4H1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.R4H1"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
        x ∈ K) ∧
    (∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            τ w = w) ↔
        ∃ x : LaurentSeries L,
          x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) ∧
          ((w : ↥K) : LaurentSeries L) = x) := by
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqM'c : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'
  have hH : R4H1.Hyp q M' ℓ H₁ := ⟨hqM'c, hℓM', hH₁⟩

  have hexτ := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ H₁ hH₁ K hK
  obtain ⟨ι₀, hι₀⟩ := hι
  subst hK
  refine ⟨fun x hx => (R4H1.Fixed.of_mem (ξ := ζ) hH ι₀ hι₀ hx).1, fun w => ⟨fun hfix => ?_, ?_⟩⟩
  ·
    have hgood := R4H1.Good.of_mem (hmM' := hH) (ξ := ζ) (ι₀ := ι₀) hι₀ w.2
    have hexτ' : ∀ ρ ∈ R4H1.Δ q M', ∃ τ : R4H1.KL L q M' H₁ ≃ₐ[L] R4H1.KL L q M' H₁,
        ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ ρ (R4H1.KL L q M' H₁) τ := fun ρ hρ => by
      obtain ⟨τ, hτ⟩ := hexτ ρ⁻¹ (Subgroup.inv_mem _ (R4H1.mem_Δ_iff.mp hρ).2)
      rw [inv_inv] at hτ
      exact ⟨τ, hτ⟩
    have hfix' : ∀ ρ ∈ R4H1.Δ q M', ∀ τ : R4H1.KL L q M' H₁ ≃ₐ[L] R4H1.KL L q M' H₁,
        ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ ρ (R4H1.KL L q M' H₁) τ → τ w = w :=
      fun ρ hρ τ hτ =>
        hfix ρ⁻¹ (Subgroup.inv_mem _ (R4H1.mem_Δ_iff.mp hρ).1) (Subgroup.inv_mem _ (R4H1.mem_Δ_iff.mp hρ).2) τ
          (by rwa [inv_inv])
    obtain ⟨k', Φ, Ψ, hΨ, hΦE, hΨE, hwe⟩ :=
      R4H1.norm_step (n := q) hH dvd_rfl ι₀ w hgood hexτ' hfix'
    obtain ⟨x, hx, hxe⟩ := R4H1.descent_step ι₀ hqM'c Φ Ψ hΨ hΦE hΨE
    refine ⟨x, hx, ?_⟩
    have hΨq : R4H1.qC (⇑Ψ) ≠ 0 := by
      intro e
      have h0 := (R4H1.qC_eq_zero_iff (ModularCurve.restrictForm (R4H1.Γ_le_Hgp dvd_rfl hH) Ψ)).mp e
      apply hΨ
      funext z
      exact DFunLike.congr_fun h0 z
    have heq : R4H1.ιB ι₀ x = R4H1.ιB ι₀ (w : LaurentSeries L) :=
      mul_right_cancel₀ hΨq (hxe.trans hwe.symm)
    exact (R4H1.ιB_injective ι₀ heq).symm
  ·
    rintro ⟨x, hx, hwx⟩ γ hγ hγ0 τ hτ
    obtain ⟨hxK, hfixed⟩ := R4H1.Fixed.of_mem (ξ := ζ) hH ι₀ hι₀ hx
    have ew : w = ⟨x, hxK⟩ := Subtype.ext hwx
    rw [ew]
    exact Subtype.ext (hfixed γ (R4H1.mem_Δ_iff.mpr ⟨hγ, hγ0⟩) τ hτ)

end S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd (solution)
