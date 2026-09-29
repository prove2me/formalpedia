-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/02f9c905-9037-5a26-b81a-e3093f7fd56a

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

namespace W1xLA
variable (m : ℕ) [NeZero m] (M' : ℕ) {ℓg : ℕ} (hℓ : ℓg ∣ M')

abbrev H1 : Subgroup (ZMod (m ^ 2 * M'))ˣ :=
  levelH m M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓ (m ^ 2))).ker

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (H1 m M' hℓ)

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' hℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {m M' hℓ}

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' hℓ ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 ∧
      ((A 1 1 : ℤ) : ZMod ℓg) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  have hℓN : ℓg ∣ m ^ 2 * M' := Dvd.dvd.mul_left hℓ (m ^ 2)
  constructor
  · rintro ⟨hA, hH⟩
    rw [Subgroup.mem_inf] at hH
    obtain ⟨hH, hK⟩ := hH
    refine ⟨Gamma0_mem.mp hA, ?_, ?_⟩
    · rw [mem_levelH_iff] at hH
      have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH
      simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
    · rw [MonoidHom.mem_ker] at hK
      have := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) hK
      simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, ZMod.cast_intCast hℓN] using this
  · rintro ⟨h10, h11, h11'⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_levelH_iff]
      ext
      simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]
    · rw [MonoidHom.mem_ker]
      ext
      simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, ZMod.cast_intCast hℓN, h11']

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

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11, -⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, -, -⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) :
    SLq m (upSL δ (q_dvd_lowerLeft_of_mem_GH hδ)) = 1 := by
  obtain ⟨h10, h11, -⟩ := (mem_GH_iff δ).mp hδ
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

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, -, -⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / m : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨m * c, ?_⟩
  push_cast
  rw [show (m : ℤ) ^ 2 * M' * c = m * (M' * (m * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]

theorem ℓ_dvd_upSL_10 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) :
    ((((upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) : SL(2, ℤ)) 1 0 : ℤ)) : ZMod ℓg) = 0 := by
  obtain ⟨h10, -, -⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  obtain ⟨e, he⟩ := hℓ
  show ((δ 1 0 / m : ℤ) : ZMod ℓg) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc, he]
  refine ⟨m * e * c, ?_⟩
  push_cast
  rw [show (m : ℤ) ^ 2 * (ℓg * e) * c = m * (ℓg * (m * e * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' hℓ) :
    ∃ δ' ∈ GH m M' hℓ, ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m γ * (δ : GL (Fin 2) ℝ) * (conjElemN m γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq m ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hδ, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨e00, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hεq
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hδ)) (inv_mem hγ)
  have h01 : (m : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01

  have hγ10ℓ : ((γ 1 0 : ℤ) : ZMod ℓg) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓ) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
  have hAD : ((γ 0 0 : ℤ) : ZMod ℓg) * ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (fun z : ℤ => (z : ZMod ℓg)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hγ10ℓ, mul_zero, sub_zero] at this
    exact this
  have hu10 : (((u 1 0 : ℤ)) : ZMod ℓg) = 0 := by rw [hu]; exact ℓ_dvd_upSL_10 hδ
  have hu11 : (((u 1 1 : ℤ)) : ZMod ℓg) = 1 := by
    obtain ⟨-, -, h⟩ := (mem_GH_iff δ).mp hδ
    rw [hu]; exact h
  have hε11 : (ε 1 1 : ℤ) = (γ 1 0 : ℤ) * ((u 0 0 : ℤ) * (-(γ 0 1 : ℤ)) + (u 0 1 : ℤ) * (γ 0 0 : ℤ)) +
      (γ 1 1 : ℤ) * ((u 1 0 : ℤ) * (-(γ 0 1 : ℤ)) + (u 1 1 : ℤ) * (γ 0 0 : ℤ)) := by
    rw [hε, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11ℓ : ((ε 1 1 : ℤ) : ZMod ℓg) = 1 := by
    rw [hε11]; push_cast; rw [hγ10ℓ, hu10, hu11]; ring_nf; rw [mul_comm] at hAD
    linear_combination hAD
  refine ⟨downSL ε h01, ?_, ?_⟩
  · rw [mem_GH_iff]
    refine ⟨?_, e11, e11ℓ⟩
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
    Γ m M' hℓ ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' hℓ := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hmM' hγ hδ
  exact ⟨δ', hδ', e⟩

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} {ℓg : ℕ} {hℓ : ℓg ∣ M'}

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M' hℓ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

section Slash

variable (hmM' : Nat.Coprime m M')
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' hℓ) k) :
    ModularForm (Γ m M' hℓ) k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

omit hmM' in
theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' hℓ) k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_mul_apply {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ m M' hℓ) k₁) (g : ModularForm (Γ m M' hℓ) k₂) :
    ⇑(sl hmM' γ hγ (f.mul g)) = ⇑(sl hmM' γ hγ f) * ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElemN_val, abs_one, one_smul]

theorem sl_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ m M' hℓ) k) :
    sl hmM' γ hγ (f + g) = sl hmM' γ hγ f + sl hmM' γ hγ g := by
  ext τ
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, ModularForm.add_apply]

theorem sl_smul {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) (f : ModularForm (Γ m M' hℓ) k) :
    ⇑(sl hmM' γ hγ (c • f)) = c • ⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_conjElemN_apply]

theorem sl_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' hℓ) k) :
    ⇑(sl hmM' γ hγ (-f)) = -⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

theorem sl_sl {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M')
    (f : ModularForm (Γ m M' hℓ) k) :
    sl hmM' δ hδ (sl hmM' γ hγ f) = sl hmM' (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_sl, conjElemN_mul, SlashAction.slash_mul]

theorem sl_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (f : ModularForm (Γ m M' hℓ) k) : sl hmM' γ hγ f = sl hmM' γ' hγ' f := by
  subst h; rfl

theorem sl_one {k : ℤ} (f : ModularForm (Γ m M' hℓ) k) : sl hmM' 1 (one_mem _) f = f := by
  ext τ
  simp only [coe_sl, conjElemN_one, SlashAction.slash_one]

theorem sl_inv_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' hℓ) k) :
    sl hmM' γ⁻¹ (inv_mem hγ) (sl hmM' γ hγ f) = f := by
  rw [sl_sl, sl_congr hmM' (mul_inv_cancel γ) _ (one_mem _), sl_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M' hℓ) k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_inv_sl hmM' γ hγ f, h]
  ext τ
  simp [coe_sl]

theorem sl_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : sl hmM' γ hγ (0 : ModularForm (Γ m M' hℓ) k) = 0 := by
  ext τ; simp [coe_sl]

theorem sl_const (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    sl hmM' γ hγ (ModularForm.const c : ModularForm (Γ m M' hℓ) 0) = ModularForm.const c := by
  ext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElemN_apply,
    det_conjElemN_val, ModularForm.const_apply]
  simp

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M' hℓ) k₁) (g : ModularForm (Γ m M' hℓ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

theorem qC_add {k : ℤ} (f g : ModularForm (Γ m M' hℓ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ m M' hℓ) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ m M' hℓ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ m M' hℓ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit [NeZero m] in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ m M' hℓ) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ m M' hℓ) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ m M' hℓ) 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

theorem qC_sum_smul {k : ℤ} (s : Finset ℕ) (c : ℕ → ℂ) (h : ℕ → ModularForm (Γ m M' hℓ) k) :
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

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M' hℓ) k₁) (f₂ : ModularForm (Γ m M' hℓ) k₂)
    (f₃ : ModularForm (Γ m M' hℓ) k₃) (f₄ : ModularForm (Γ m M' hℓ) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ m M' hℓ) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
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

theorem slash_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M' hℓ) k₁) (f₂ : ModularForm (Γ m M' hℓ) k₂)
    (f₃ : ModularForm (Γ m M' hℓ) k₃) (f₄ : ModularForm (Γ m M' hℓ) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    (⇑(sl hmM' γ hγ f₁) * ⇑(sl hmM' γ hγ f₂) : ℍ → ℂ) = ⇑(sl hmM' γ hγ f₃) * ⇑(sl hmM' γ hγ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] conjElemN m γ) h
  rw [ModularForm.mul_slash] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash]
  simpa only [coe_sl, det_conjElemN_val, abs_one, one_smul] using h'

theorem qC_sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {g : ModularForm (Γ m M' hℓ) k}
    (hg : g ≠ 0) : qC (sl hmM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hmM' γ hγ hg ((qC_eq_zero_iff _).mp h)

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

section Img

variable (hℓ) (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def IsImgC (w w' : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γ m M' hℓ) k), g ≠ 0 ∧ w = qC f / qC g ∧
    w' * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f)

variable {hℓ hmM' γ hγ}

theorem IsImgC.apply_rep {w w' : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ w w') {k : ℤ}
    (f g : ModularForm (Γ m M' hℓ) k) (hg : g ≠ 0) (hw : w = qC f / qC g) :
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

theorem IsImgC.unique {w y y' : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ w y) (h' : IsImgC hℓ hmM' γ hγ w y') :
    y = y' := by
  obtain ⟨k, f, g, hg, hw, hy'⟩ := h'
  have hy := h.apply_rep f g hg hw
  rw [← hy'] at hy
  exact mul_right_cancel₀ (qC_sl_ne_zero hmM' γ hγ hg) hy

theorem IsImgC.hasRep {w y : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ w y) :
    ∃ (k : ℤ) (f g : ModularForm (Γ m M' hℓ) k), g ≠ 0 ∧ w = qC f / qC g := by
  obtain ⟨k, f, g, hg, hw, _⟩ := h
  exact ⟨k, f, g, hg, hw⟩

theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ m M' hℓ) k₁} {g₂ : ModularForm (Γ m M' hℓ) k₂}
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) : g₁.mul g₂ ≠ 0 := by
  intro h
  have : qC (⇑(g₁.mul g₂)) = 0 := by rw [h, ModularForm.coe_zero, qC_zero]
  rw [ModularForm.coe_mul, qC_mul] at this
  rcases mul_eq_zero.mp this with e | e
  · exact h₁ ((qC_eq_zero_iff _).mp e)
  · exact h₂ ((qC_eq_zero_iff _).mp e)

theorem IsImgC.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hℓ hmM' γ hγ x₁ y₁) (h₂ : IsImgC hℓ hmM' γ hγ x₂ y₂) :
    IsImgC hℓ hmM' γ hγ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, hg₂, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, mul_ne_zero_form hg₁ hg₂, ?_, ?_⟩
  · rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul, div_mul_div_comm]
  · rw [sl_mul_apply, sl_mul_apply, qC_mul, qC_mul, ← hy₁, ← hy₂]
    ring

theorem IsImgC.add {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hℓ hmM' γ hγ x₁ y₁) (h₂ : IsImgC hℓ hmM' γ hγ x₂ y₂) :
    IsImgC hℓ hmM' γ hγ (x₁ + x₂) (y₁ + y₂) := by
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

theorem IsImgC.neg {x y : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ x y) : IsImgC hℓ hmM' γ hγ (-x) (-y) := by
  obtain ⟨k, f, g, hg, rfl, hy⟩ := h
  refine ⟨k, -f, g, hg, ?_, ?_⟩
  · rw [ModularForm.coe_neg, qC_neg]
    exact (neg_div (qC ⇑g) (qC ⇑f)).symm
  · rw [sl_neg, qC_neg, ← hy]
    ring

theorem one_ne_zero_form : (1 : ModularForm (Γ m M' hℓ) 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm (Γ m M' hℓ) 0 => qC (⇑F)) h
  simp only [ModularForm.one_coe_eq_one, qC_one, ModularForm.coe_zero, qC_zero] at this
  exact one_ne_zero this

theorem IsImgC.const (c : ℂ) : IsImgC hℓ hmM' γ hγ (HahnSeries.C c) (HahnSeries.C c) := by
  refine ⟨0, ModularForm.const c, 1, one_ne_zero_form, ?_, ?_⟩
  · rw [qC_const, ModularForm.one_coe_eq_one, qC_one, div_one]
  · have h1 : sl hmM' γ hγ (1 : ModularForm (Γ m M' hℓ) 0) = 1 := by
      have := sl_const (hℓ := hℓ) hmM' γ hγ (1 : ℂ)
      have e : (ModularForm.const 1 : ModularForm (Γ m M' hℓ) 0) = 1 := by
        ext τ; simp
      rwa [e] at this
    rw [h1, sl_const, ModularForm.one_coe_eq_one, qC_one, mul_one, qC_const]

theorem IsImgC.one : IsImgC hℓ hmM' γ hγ 1 1 := by
  simpa using IsImgC.const (hmM' := hmM') (γ := γ) (hγ := hγ) 1

theorem IsImgC.zero : IsImgC hℓ hmM' γ hγ 0 0 := by
  simpa using IsImgC.const (hmM' := hmM') (γ := γ) (hγ := hγ) 0

theorem IsImgC.inv {x y : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ x y) : IsImgC hℓ hmM' γ hγ x⁻¹ y⁻¹ := by
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

theorem IsImgC.symm {x y : LaurentSeries ℂ} (h : IsImgC hℓ hmM' γ hγ x y)
    (hyS : ∃ (k : ℤ) (P Q : ModularForm (Γ m M' hℓ) k), Q ≠ 0 ∧ y = qC P / qC Q) :
    IsImgC hℓ hmM' γ⁻¹ (inv_mem hγ) y x := by
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
    (h : IsImgC hℓ hmM' γ hγ x y) : IsImgC hℓ hmM' γ' hγ' x y := by
  subst e; exact h

end Img
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {hℓ : ℓg ∣ M'} {L : Type} [Field L] [CharZero L]

section Emb

abbrev KL (L : Type) [Field L] [CharZero L] (m M' : ℕ) {ℓg : ℕ} (hℓ : ℓg ∣ M') : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') (H1 m M' hℓ))

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

theorem qC_ne_zero_of_intSeriesC {k : ℤ} {g : ModularForm (Γ m M' hℓ) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ m M' hℓ) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

end Emb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

section FAG

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {ℓg : ℕ} {hℓ : ℓg ∣ M'} (hmM' : Nat.Coprime m M')
variable {L : Type} [Field L] [CharZero L] (n : ℕ) (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = Complex.exp (2 * Real.pi * Complex.I / n))

include hι₀ in

theorem isImgC_of_isLevelAutAt (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (σ : KL L m M' hℓ ≃ₐ[L] KL L m M' hℓ)
    (hσ : IsLevelAutAt L n ξ m (m ^ 2 * M') (H1 m M' hℓ) γ (KL L m M' hℓ) σ) (X : KL L m M' hℓ) :
    IsImgC hℓ hmM' γ hγ (ιB ι₀ (X : LaurentSeries L)) (ιB ι₀ (σ X : LaurentSeries L)) := by

  suffices key : ∀ (x : LaurentSeries L), x ∈ KL L m M' hℓ → ∀ hx : x ∈ KL L m M' hℓ,
      IsImgC hℓ hmM' γ hγ (ιB ι₀ x) (ιB ι₀ (σ ⟨x, hx⟩ : LaurentSeries L)) from key X X.2 X.2
  intro x hx
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    intro hx
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    · have e : σ ⟨algebraMap L (LaurentSeries L) c, hx⟩ = algebraMap L (KL L m M' hℓ) c :=
        (congrArg σ (Subtype.ext rfl)).trans (σ.commutes c)
      rw [e]
      show IsImgC hℓ hmM' γ hγ (ιB ι₀ (algebraMap L (LaurentSeries L) c)) (ιB ι₀ (algebraMap L (LaurentSeries L) c))
      rw [← C_eq_algebraMap, ιB_C]
      exact IsImgC.const _
    ·
      revert hx
      change z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M' hℓ)) at hz
      induction hz using Subfield.closure_induction with
      | mem y hy =>
        intro hx
        rcases hy with ⟨r, rfl⟩ | hy
        · have e0 : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (r : L) := by
            rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
            simp
          have e : σ ⟨coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r), hx⟩ = algebraMap L (KL L m M' hℓ) (r : L) :=
            (congrArg σ (Subtype.ext e0)).trans (σ.commutes (r : L))
          rw [e, e0]
          show IsImgC hℓ hmM' γ hγ (ιB ι₀ (algebraMap L (LaurentSeries L) (r : L))) (ιB ι₀ (algebraMap L (LaurentSeries L) (r : L)))
          rw [← C_eq_algebraMap, ιB_C]
          exact IsImgC.const _
        · obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
          refine ⟨k, f, g, ne_zero_of_intSeriesC_ne_zero hg hg0, ?_, ?_⟩
          · rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
          · exact hσ k f g pf pg hf hg hg0 ⟨_, hx⟩ rfl ι₀ hι₀
      | one =>
        intro hx
        have e : σ ⟨coeffEmb L 1, hx⟩ = 1 := by
          have h1 : (⟨coeffEmb L 1, hx⟩ : KL L m M' hℓ) = 1 := Subtype.ext (map_one _)
          rw [h1, map_one]
        rw [e]
        simp only [map_one, OneMemClass.coe_one]
        exact IsImgC.one
      | add a b ha hb iha ihb =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L ha
        have hb' : coeffEmb L b ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L hb
        have e : σ ⟨coeffEmb L (a + b), hx⟩ = σ ⟨_, ha'⟩ + σ ⟨_, hb'⟩ := by
          rw [← map_add]; exact congrArg σ (Subtype.ext (map_add _ _ _))
        rw [e, map_add, map_add, AddMemClass.coe_add, map_add]
        exact (iha ha').add (ihb hb')
      | neg a ha iha =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L ha
        have e : σ ⟨coeffEmb L (-a), hx⟩ = -σ ⟨_, ha'⟩ := by
          rw [← map_neg]; exact congrArg σ (Subtype.ext (map_neg _ _))
        rw [e, map_neg, map_neg, NegMemClass.coe_neg, map_neg]
        exact (iha ha').neg
      | inv a ha iha =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L ha
        have e : σ ⟨coeffEmb L a⁻¹, hx⟩ = (σ ⟨_, ha'⟩)⁻¹ := by
          rw [← map_inv₀]; exact congrArg σ (Subtype.ext (map_inv₀ _ _))
        rw [e]
        have h' := (iha ha').inv
        simp only [map_inv₀, IntermediateField.coe_inv] at h' ⊢
        exact h'
      | mul a b ha hb iha ihb =>
        intro hx
        have ha' : coeffEmb L a ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L ha
        have hb' : coeffEmb L b ∈ KL L m M' hℓ := coeffEmb_mem_laurentBaseChange L hb
        have e : σ ⟨coeffEmb L (a * b), hx⟩ = σ ⟨_, ha'⟩ * σ ⟨_, hb'⟩ := by
          rw [← map_mul]; exact congrArg σ (Subtype.ext (map_mul _ _ _))
        rw [e, map_mul, map_mul, MulMemClass.coe_mul, map_mul]
        exact (iha ha').mul (ihb hb')
  | one =>
    intro hx
    have e : σ ⟨1, hx⟩ = 1 := by
      have h1 : (⟨1, hx⟩ : KL L m M' hℓ) = 1 := Subtype.ext rfl
      rw [h1, map_one]
    rw [e]
    simp only [map_one, OneMemClass.coe_one]
    exact IsImgC.one
  | add a b ha hb iha ihb =>
    intro hx
    have ha' : a ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact ha
    have hb' : b ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact hb
    have e : σ ⟨a + b, hx⟩ = σ ⟨a, ha'⟩ + σ ⟨b, hb'⟩ := by rw [← map_add]; rfl
    rw [e, map_add, AddMemClass.coe_add, map_add]
    exact (iha ha').add (ihb hb')
  | neg a ha iha =>
    intro hx
    have ha' : a ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact ha
    have e : σ ⟨-a, hx⟩ = -σ ⟨a, ha'⟩ := by rw [← map_neg]; rfl
    rw [e, map_neg, NegMemClass.coe_neg, map_neg]
    exact (iha ha').neg
  | inv a ha iha =>
    intro hx
    have ha' : a ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact ha
    have e : σ ⟨a⁻¹, hx⟩ = (σ ⟨a, ha'⟩)⁻¹ := by rw [← map_inv₀]; rfl
    rw [e]
    have h' := (iha ha').inv
    simp only [map_inv₀, IntermediateField.coe_inv] at h' ⊢
    exact h'
  | mul a b ha hb iha ihb =>
    intro hx
    have ha' : a ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact ha
    have hb' : b ∈ KL L m M' hℓ := by rw [mem_laurentBaseChange_iff]; exact hb
    have e : σ ⟨a * b, hx⟩ = σ ⟨a, ha'⟩ * σ ⟨b, hb'⟩ := by rw [← map_mul]; rfl
    rw [e, map_mul, MulMemClass.coe_mul, map_mul]
    exact (iha ha').mul (ihb hb')

end FAG
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

end W1xLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq.W1xLA"

open scoped MatrixGroups ModularForm

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)
    (X Y : ↥K) (k : ℤ)
    (F G : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) k)
    (hG : G ≠ 0)
    (hX : ModularCurve.coeffMap ι ((X : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F)))
    (hY : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ModularCurve.coeffMap ι ((Y : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑G ∣[k] ModularCurve.FullLevel.conjElemN q γ⁻¹)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
          (⇑F ∣[k] ModularCurve.FullLevel.conjElemN q γ⁻¹))) :
    τ X = Y := by
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hmM' : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'
  subst hH₁
  subst hK
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hℓC : (ℓg : ℂ) ≠ 0 := by exact_mod_cast hℓg.ne_zero
  have hι' : ι (ξ ^ ℓg) = Complex.exp (2 * Real.pi * Complex.I / q) := by
    rw [map_pow, hι, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have h1 := W1xLA.isImgC_of_isLevelAutAt (hℓ := hℓgM') hmM' q (ξ ^ ℓg) ι hι' γ⁻¹ (inv_mem hγ) τ hτ X
  have hGq : W1xLA.qC (⇑G) ≠ 0 := fun e => hG ((W1xLA.qC_eq_zero_iff (hℓ := hℓgM') G).mp e)
  have h2 : W1xLA.IsImgC hℓgM' hmM' γ⁻¹ (inv_mem hγ) (W1xLA.ιB ι (X : LaurentSeries L)) (W1xLA.ιB ι (Y : LaurentSeries L)) := by
    refine ⟨k, F, G, hG, ?_, ?_⟩
    · rw [eq_div_iff hGq]; exact hX
    · exact hY
  have h3 := h1.unique h2
  exact Subtype.ext (W1xLA.ιB_injective ι h3)

end S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq (solution)
