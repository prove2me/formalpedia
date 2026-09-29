-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f7048784-0c7d-5fb4-ab5e-9edb928069cb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom

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

theorem det_conjElemN_val (γ : SL(2, ℤ)) : ((conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

namespace W1xLA
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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M') k₁) (g : ModularForm (Γ m M') k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Emb

abbrev KL (L : Type) [Field L] [CharZero L] (m M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') (levelH m M'))

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

abbrev ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

omit [NeZero m] in
theorem ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

theorem main (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq (q * ℓ)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ τ : ↥(KL L (q * ℓ) M') ≃ₐ[L] ↥(KL L (q * ℓ) M'),
      IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L (q * ℓ) M') τ := by
  have hcop : Nat.Coprime (q * ℓ) M' :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM')
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM')
  exact ⟨τEquiv hcop ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ), isLevelAutAt_τEquiv hcop ξ ι₀ hι₀ γ⁻¹ (inv_mem hγ)⟩

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom.W1xLA"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ := by
  intro γ hγ
  subst hK
  obtain ⟨ι₀, hι₀'⟩ := hι
  have hι₀ : ι₀ ξ = W1xLA.eq (q * ℓ) := by
    rw [hι₀']
    simp only [W1xLA.eq, Nat.cast_mul]
  exact W1xLA.main q M' hqM' ℓ hℓM' L ξ ι₀ hι₀ γ hγ

end S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom (solution)
