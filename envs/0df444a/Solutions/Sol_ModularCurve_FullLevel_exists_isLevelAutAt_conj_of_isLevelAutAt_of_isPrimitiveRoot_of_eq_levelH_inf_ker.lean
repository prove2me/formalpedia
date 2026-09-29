-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4d60e0d9-ef67-5008-b7cb-7fc9c93e56ec

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_integralClosure_exists_complex_ringEquiv_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1TW
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

end W1TW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

structure W1TW.Hyp (m M' ℓg : ℕ) (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Prop where
  cop : Nat.Coprime m M'
  dvd : ℓg ∣ M'
  eq : H₁ = levelH m M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left dvd (m ^ 2))).ker

namespace W1TW
variable (m : ℕ) [NeZero m] (M' : ℕ)

abbrev GH (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') H₁

abbrev Γ (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GH m M' H₁ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {m M'} {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}

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

theorem SLq_eq_iff (A B : SL(2, ℤ)) : SLq m A = SLq m B ↔ ∀ i j, ((A i j : ℤ) : ZMod m) = ((B i j : ℤ) : ZMod m) := by
  constructor
  · intro h i j
    rw [← SLq_apply, ← SLq_apply, h]
  · intro h
    ext i j
    rw [SLq_apply, SLq_apply, h]

theorem intCast_zmod_of_dvd {a b : ℕ} (h : a ∣ b) {x : ℤ} {y : ℤ} (hxy : ((x : ℤ) : ZMod b) = (y : ZMod b)) :
    ((x : ℤ) : ZMod a) = (y : ZMod a) := by
  have := congrArg (ZMod.castHom h (ZMod a)) hxy
  rwa [map_intCast, map_intCast] at this

theorem downSL_eq (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr m)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← downSL_coe ε h, inv_mul_cancel_left]

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

variable (hqM' : Hyp m M' ℓg H₁)
include hqM'

theorem isCoprime_q_M' : IsCoprime (m : ℤ) (M' : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact hqM'.cop

theorem coprime_q_M' : Nat.Coprime m M' := hqM'.cop

omit [NeZero m] in
theorem M'_ne_zero [NeZero M'] : M' ≠ 0 := NeZero.ne M'

omit [NeZero m] in
theorem ℓg_dvd_level : ℓg ∣ m ^ 2 * M' := Dvd.dvd.mul_left hqM'.dvd (m ^ 2)

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' H₁ ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 ∧
      ((A 1 1 : ℤ) : ZMod ℓg) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff, hqM'.eq]
  constructor
  · rintro ⟨hA, hHL⟩
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_levelH_iff] at hHL
    obtain ⟨hH, hL⟩ := hHL
    refine ⟨Gamma0_mem.mp hA, ?_, ?_⟩
    · have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH
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

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11, -⟩ := (mem_GH_iff hqM' δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have := congrArg (fun z : ℤ => (z : ZMod m)) (det2 δ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem upperLeft_of_mem_GH_ℓ {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) : ((δ 0 0 : ℤ) : ZMod ℓg) = 1 := by
  obtain ⟨h10, -, h11⟩ := (mem_GH_iff hqM' δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod ℓg) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (ℓg_dvd_level hqM')) h10
  have := congrArg (fun z : ℤ => (z : ZMod ℓg)) (det2 δ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, -, -⟩ := (mem_GH_iff hqM' δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) :
    SLq m (upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ)) = 1 := by
  obtain ⟨h10, h11, -⟩ := (mem_GH_iff hqM' δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod m) = 1
    exact upperLeft_of_mem_GH hqM' hδ
  · show (((m : ℤ) * δ 0 1 : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / m : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  · show ((δ 1 1 : ℤ) : ZMod m) = 1
    exact h11

theorem upSL_mod_ℓ {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) :
    (((upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ)) 0 0 : ℤ) : ZMod ℓg) = 1 ∧
    (((upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ)) 1 0 : ℤ) : ZMod ℓg) = 0 ∧
    (((upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ)) 1 1 : ℤ) : ZMod ℓg) = 1 := by
  obtain ⟨h10, -, h11⟩ := (mem_GH_iff hqM' δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  refine ⟨?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod ℓg) = 1
    exact upperLeft_of_mem_GH_ℓ hqM' hδ
  · show ((δ 1 0 / m : ℤ) : ZMod ℓg) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    obtain ⟨e, he⟩ := hqM'.dvd
    refine ⟨m * e * c, ?_⟩
    push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * M' * c) by ring, Int.mul_ediv_cancel_left _ (mneZ m), he]
    push_cast; ring
  · show ((δ 1 1 : ℤ) : ZMod ℓg) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, -, -⟩ := (mem_GH_iff hqM' δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / m : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨m * c, ?_⟩
  push_cast
  rw [show (m : ℤ) ^ 2 * M' * c = m * (M' * (m * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]

theorem lowerLeft_mod_ℓ_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : ((γ 1 0 : ℤ) : ZMod ℓg) = 0 := by
  have := Gamma0_mem.mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hqM'.dvd) this

theorem diag_mod_ℓ_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    ((γ 0 0 : ℤ) : ZMod ℓg) * ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
  have h10 := lowerLeft_mod_ℓ_of_mem_Gamma0 hqM' hγ
  have := congrArg (fun z : ℤ => (z : ZMod ℓg)) (det2 γ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h10, mul_zero, sub_zero] at this
  exact this

theorem downSL_mem_GH {ε : SL(2, ℤ)} (hε : SLq m ε = 1) (hM : (M' : ℤ) ∣ ε 1 0)
    (hℓ : ((ε 1 1 : ℤ) : ZMod ℓg) = 1) :
    ∃ h01 : (m : ℤ) ∣ ε 0 1, downSL ε h01 ∈ GH m M' H₁ := by
  obtain ⟨_, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hε
  have h01 : (m : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨h01, ?_⟩
  rw [mem_GH_iff hqM']
  refine ⟨?_, e11, hℓ⟩
  show (((m : ℤ) * ε 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (m : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
  obtain ⟨c, hc⟩ := (isCoprime_q_M' hqM').mul_dvd hq hM
  refine ⟨c, ?_⟩
  rw [hc]; push_cast; ring

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H₁) :
    ∃ δ' ∈ GH m M' H₁, ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m γ * (δ : GL (Fin 2) ℝ) * (conjElemN m γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεm : SLq m ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hqM' hδ, mul_one, map_inv, mul_inv_cancel]
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hqM' hδ)) (inv_mem hγ)
  have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
  have hℓ : ((ε 1 1 : ℤ) : ZMod ℓg) = 1 := by
    obtain ⟨u00, u10, u11⟩ := upSL_mod_ℓ hqM' hδ
    rw [← hu] at u00 u10 u11
    have g10 := lowerLeft_mod_ℓ_of_mem_Gamma0 hqM' hγ
    have gdet := diag_mod_ℓ_of_mem_Gamma0 hqM' hγ
    have e1 : ((γ * u) 1 0 : ℤ) = γ 1 0 * u 0 0 + γ 1 1 * u 1 0 := mul_apply_10 γ u
    have e2 : ((γ * u) 1 1 : ℤ) = γ 1 0 * u 0 1 + γ 1 1 * u 1 1 := mul_apply_11 γ u
    have e3 : (ε 1 1 : ℤ) = (γ * u) 1 0 * (γ⁻¹) 0 1 + (γ * u) 1 1 * (γ⁻¹) 1 1 := by
      rw [hε]; exact mul_apply_11 _ _
    rw [e3, e1, e2, inv_apply_01, inv_apply_11]
    push_cast
    rw [g10, u10, u11]
    linear_combination gdet
  obtain ⟨h01, hmem⟩ := downSL_mem_GH hqM' hεm hM hℓ
  refine ⟨downSL ε h01, hmem, ?_⟩
  have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hqM' hδ)
  rw [← hu] at hup
  have e2 : (u : GL (Fin 2) ℝ) = Dr m * (δ : GL (Fin 2) ℝ) * (Dr m)⁻¹ := by
    rw [← hup, mul_inv_cancel_right]
  rw [downSL_eq, hε]
  simp only [map_mul, map_inv]
  rw [e2, conjElemN_eq]
  group

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ m M' H₁ ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' H₁ := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hqM' hγ hδ
  exact ⟨δ', hδ', e⟩

end W1TW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

namespace W1TW

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ}

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M' H₁).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

section Slash

variable (hmM' : Hyp m M' ℓg H₁)
include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    ModularForm (Γ m M' H₁) k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

omit hmM' in
theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_mul_apply {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ m M' H₁) k₁) (g : ModularForm (Γ m M' H₁) k₂) :
    ⇑(sl hmM' γ hγ (f.mul g)) = ⇑(sl hmM' γ hγ f) * ⇑(sl hmM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElemN_val, abs_one, one_smul]

theorem sl_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ m M' H₁) k) :
    sl hmM' γ hγ (f + g) = sl hmM' γ hγ f + sl hmM' γ hγ g := by
  ext τ
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, ModularForm.add_apply]

theorem sl_smul {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) (f : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ (c • f)) = c • ⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_conjElemN_apply]

theorem sl_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    ⇑(sl hmM' γ hγ (-f)) = -⇑(sl hmM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

theorem sl_sl {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M')
    (f : ModularForm (Γ m M' H₁) k) :
    sl hmM' δ hδ (sl hmM' γ hγ f) = sl hmM' (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_sl, conjElemN_mul, SlashAction.slash_mul]

theorem sl_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (f : ModularForm (Γ m M' H₁) k) : sl hmM' γ hγ f = sl hmM' γ' hγ' f := by
  subst h; rfl

theorem sl_one {k : ℤ} (f : ModularForm (Γ m M' H₁) k) : sl hmM' 1 (one_mem _) f = f := by
  ext τ
  simp only [coe_sl, conjElemN_one, SlashAction.slash_one]

theorem sl_inv_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H₁) k) :
    sl hmM' γ⁻¹ (inv_mem hγ) (sl hmM' γ hγ f) = f := by
  rw [sl_sl, sl_congr hmM' (mul_inv_cancel γ) _ (one_mem _), sl_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M' H₁) k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_inv_sl hmM' γ hγ f, h]
  ext τ
  simp [coe_sl]

theorem sl_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : sl hmM' γ hγ (0 : ModularForm (Γ m M' H₁) k) = 0 := by
  ext τ; simp [coe_sl]

theorem sl_const (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    sl hmM' γ hγ (ModularForm.const c : ModularForm (Γ m M' H₁) 0) = ModularForm.const c := by
  ext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElemN_apply,
    det_conjElemN_val, ModularForm.const_apply]
  simp

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ m M' H₁) k₁) (g : ModularForm (Γ m M' H₁) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

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

omit [NeZero m] in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ m M' H₁) 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

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

variable (hmM' : Hyp m M' ℓg H₁)
include hmM'

theorem slash_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ m M' H₁) k₁) (f₂ : ModularForm (Γ m M' H₁) k₂)
    (f₃ : ModularForm (Γ m M' H₁) k₃) (f₄ : ModularForm (Γ m M' H₁) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    (⇑(sl hmM' γ hγ f₁) * ⇑(sl hmM' γ hγ f₂) : ℍ → ℂ) = ⇑(sl hmM' γ hγ f₃) * ⇑(sl hmM' γ hγ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] conjElemN m γ) h
  rw [ModularForm.mul_slash] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash]
  simpa only [coe_sl, det_conjElemN_val, abs_one, one_smul] using h'

theorem qC_sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {g : ModularForm (Γ m M' H₁) k}
    (hg : g ≠ 0) : qC (sl hmM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hmM' γ hγ hg ((qC_eq_zero_iff _).mp h)

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

end W1TW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

namespace W1TW

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} {ℓg : ℕ} {H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Emb

abbrev KL (L : Type) [Field L] [CharZero L] (m M' : ℕ) (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField (m ^ 2 * M') H₁)

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

theorem qC_ne_zero_of_intSeriesC {k : ℤ} {g : ModularForm (Γ m M' H₁) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ m M' H₁) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

end Emb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section Helpers

omit [NeZero M'] in
theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ m M' H₁) k₁} {g₂ : ModularForm (Γ m M' H₁) k₂}
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) : g₁.mul g₂ ≠ 0 := by
  intro h
  have : qC (⇑(g₁.mul g₂)) = 0 := by rw [h, ModularForm.coe_zero, qC_zero]
  rw [ModularForm.coe_mul, qC_mul] at this
  rcases mul_eq_zero.mp this with e | e
  · exact h₁ ((qC_eq_zero_iff _).mp e)
  · exact h₂ ((qC_eq_zero_iff _).mp e)

omit [NeZero m] [NeZero M'] in

theorem exists_ratCast_of_isIntegralQExp {φ : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp φ p) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 φ).coeff n = (r : ℂ) :=
  ⟨((PowerSeries.coeff n p : ℤ) : ℚ), by rw [← h.coeff n]; push_cast; rfl⟩

omit [NeZero M'] in

theorem isIntegralQExp_mul {k₁ k₂ : ℤ} {f : ModularForm (Γ m M' H₁) k₁} {g : ModularForm (Γ m M' H₁) k₂}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g).symm

omit [NeZero m] [NeZero M'] in

theorem coeffMap_C (σ : ℂ →+* ℂ) (c : ℂ) : coeffMap σ (HahnSeries.C c) = HahnSeries.C (σ c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

omit [NeZero m] [NeZero M'] in

theorem coeffMap_qC_of_ratCast (σ : ℂ →+* ℂ) {φ : ℍ → ℂ}
    (hφ : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 φ).coeff n = (r : ℂ)) : coeffMap σ (qC φ) = qC φ := by
  ext n
  simp only [qC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero σ
  · obtain ⟨r, hr⟩ := hφ n.natAbs
    rw [hr, map_ratCast]

omit [NeZero m] [NeZero M'] in
theorem coeffMap_injective_of_complex (σ : ℂ →+* ℂ) : Function.Injective (coeffMap σ) := fun x y h =>
  HahnSeries.ext (funext fun n => σ.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

private abbrev _root_.W1TW.eq (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

p2m_export "W1TW" "eq"
omit [NeZero M'] in
theorem sum_exp_smul_eq {k : ℤ} (s : ℕ) (h : ℕ → ModularForm (Γ m M' H₁) k) :
    (∑ j ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / m) •
        (⇑(h j) : ℍ → ℂ)) =
      ∑ j ∈ Finset.range m, (eq m ^ s) ^ j • (⇑(h j) : ℍ → ℂ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← pow_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

variable (hmM' : Hyp m M' ℓg H₁)
include hmM'

theorem recip {k : ℤ} (hk : Even k) (F : ModularForm (Γ m M' H₁) k) (pF : PowerSeries ℤ) (hF : IsIntegralQExp F pF)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ h : ℕ → ModularForm (Γ m M' H₁) k,
      (∀ j n : ℕ, ∃ r : ℚ, (qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)) (hs : Nat.Coprime s m) (hγ' : γ' ∈ Gamma0 M'),
        ((γ' 1 1 : ℤ) : ZMod ℓg) = ((γ 1 1 : ℤ) : ZMod ℓg) →
        !![(1 : ZMod m), 0; 0, (s : ZMod m)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, (s : ZMod m)] →
        qC (sl hmM' γ' hγ' F) = ∑ j ∈ Finset.range m, HahnSeries.C ((eq m ^ s) ^ j) * qC (h j) := by
  obtain ⟨h, hrat, hrec⟩ :=
    ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker m M'
      hmM'.cop ℓg hmM'.dvd H₁ hmM'.eq hk F (exists_ratCast_of_isIntegralQExp hF) γ hγ
  refine ⟨h, hrat, fun s γ' hs hγ' hd hmat => ?_⟩
  have e := hrec s γ' hs hγ' hd hmat
  rw [sum_exp_smul_eq] at e
  change qC (⇑F ∣[k] conjElemN m γ') = _
  rw [e, qC_sum_smul]

end Helpers
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section AutC

open Polynomial

omit [NeZero m] [NeZero M'] in

theorem exists_complex_ringEquiv_apply_eq_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {w₁ w₂ : ℂ}
    (h₁ : IsPrimitiveRoot w₁ n) (h₂ : IsPrimitiveRoot w₂ n) : ∃ σ : ℂ ≃+* ℂ, σ w₁ = w₂ := by
  classical
  haveI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn.ne'⟩

  set A : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ with hA
  haveI : Algebra.IsAlgebraic ℚ A := by rw [hA]; exact algebraicClosure.isAlgebraic ℚ ℂ
  have hint₁ : IsIntegral ℤ w₁ := h₁.isIntegral hn
  have hw₁A : w₁ ∈ A := (mem_algebraicClosure_iff' (F := ℚ) (E := ℂ)).2 hint₁.tower_top
  set a₁ : A := ⟨w₁, hw₁A⟩ with ha₁
  have hmin : minpoly ℚ a₁ = cyclotomic n ℚ := by
    have e : minpoly ℚ a₁ = minpoly ℚ w₁ := by
      have := minpoly.algHom_eq (IntermediateField.val A) (IntermediateField.val A).injective a₁
      exact this.symm
    rw [e]
    exact (cyclotomic_eq_minpoly_rat h₁ hn).symm
  have hroot : w₂ ∈ (minpoly ℚ a₁).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr h₂).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ a₁] at hroot
  obtain ⟨ψ, hψ⟩ := hroot

  set B : Subalgebra ℤ ℂ := integralClosure ℤ ℂ with hB
  have hmemA : ∀ b : B, (b : ℂ) ∈ A := fun b =>
    (mem_algebraicClosure_iff' (F := ℚ) (E := ℂ)).2 ((mem_integralClosure_iff ℤ ℂ).1 b.2).tower_top
  let incl : B →+* A :=
    { toFun := fun b => ⟨(b : ℂ), hmemA b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  set φ : B →+* ℂ := ψ.toRingHom.comp incl with hφ
  set ψ₀ : B →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom with hψ₀
  obtain ⟨σ, hσ⟩ := integralClosure.exists_complex_ringEquiv_apply_eq ℂ φ ψ₀
  have hw₁B : w₁ ∈ B := (mem_integralClosure_iff ℤ ℂ).2 hint₁
  have hσw₁B : σ w₁ ∈ B :=
    (mem_integralClosure_iff ℤ ℂ).2 ((h₁.map_of_injective σ.injective).isIntegral hn)
  have e := hσ ⟨w₁, hw₁B⟩ ⟨σ w₁, hσw₁B⟩ rfl
  refine ⟨σ, ?_⟩
  have e1 : φ ⟨w₁, hw₁B⟩ = w₂ := by
    rw [hφ, RingHom.comp_apply]
    change ψ (incl ⟨w₁, hw₁B⟩) = w₂
    have : incl ⟨w₁, hw₁B⟩ = a₁ := Subtype.ext rfl
    rw [this]
    exact hψ
  have e2 : ψ₀ ⟨σ w₁, hσw₁B⟩ = σ w₁ := rfl
  rw [e1, e2] at e
  exact e.symm

end AutC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section Reps

def liftSL (X : SL(2, ZMod (m * M'))) : SL(2, ℤ) :=
  Classical.choose (ModularCurve.surjective_specialLinearGroup_map_zmod (m * M') X)

theorem liftSL_spec (X : SL(2, ZMod (m * M'))) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (m * M'))) (liftSL X) = X :=
  Classical.choose_spec (ModularCurve.surjective_specialLinearGroup_map_zmod (m * M') X)

theorem liftSL_entry (X : SL(2, ZMod (m * M'))) (i j : Fin 2) :
    (((liftSL X) i j : ℤ) : ZMod (m * M')) = X i j := by
  have := congrArg (fun Y : SL(2, ZMod (m * M')) => Y i j) (liftSL_spec X)
  simpa using this

def red (γ : SL(2, ℤ)) (i j : Fin 2) : ZMod (m * M') := ((γ i j : ℤ) : ZMod (m * M'))

omit [NeZero m] [NeZero M'] in
theorem red_det (γ : SL(2, ℤ)) : red (m := m) (M' := M') γ 0 0 * red γ 1 1 - red γ 0 1 * red γ 1 0 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod (m * M'))) hdet
  push_cast at this
  exact this

def Xt (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) : SL(2, ZMod (m * M')) :=
  ⟨!![red γ 0 0, (t : ZMod (m * M')) * red γ 0 1; ((t⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) * red γ 1 0, red γ 1 1],
    by
      rw [Matrix.det_fin_two_of]
      have h := red_det (m := m) (M' := M') γ
      have ht : (t : ZMod (m * M')) * ((t⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) = 1 := Units.mul_inv t
      linear_combination h - (red γ 0 1 * red γ 1 0) * ht⟩

def γt (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) : SL(2, ℤ) := liftSL (Xt γ t)

theorem γt_red (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) (i j : Fin 2) :
    (((γt γ t) i j : ℤ) : ZMod (m * M')) = Xt γ t i j :=
  liftSL_entry (Xt γ t) i j

theorem γt_red00 (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) :
    (((γt γ t) 0 0 : ℤ) : ZMod (m * M')) = ((γ 0 0 : ℤ) : ZMod (m * M')) := by
  rw [γt_red]; rfl
theorem γt_red01 (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) :
    (((γt γ t) 0 1 : ℤ) : ZMod (m * M')) = (t : ZMod (m * M')) * ((γ 0 1 : ℤ) : ZMod (m * M')) := by
  rw [γt_red]; rfl
theorem γt_red10 (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) :
    (((γt γ t) 1 0 : ℤ) : ZMod (m * M')) = ((t⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) * ((γ 1 0 : ℤ) : ZMod (m * M')) := by
  rw [γt_red]; rfl
theorem γt_red11 (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) :
    (((γt γ t) 1 1 : ℤ) : ZMod (m * M')) = ((γ 1 1 : ℤ) : ZMod (m * M')) := by
  rw [γt_red]; rfl

theorem γt_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (t : (ZMod (m * M'))ˣ) : γt (m := m) γ t ∈ Gamma0 M' := by
  rw [Gamma0_mem] at hγ ⊢
  have h := γt_red10 (m := m) (M' := M') γ t
  have := congrArg (ZMod.castHom (dvd_mul_left M' m) (ZMod M')) h
  rw [map_intCast, map_mul, map_intCast, hγ, mul_zero] at this
  exact this

theorem γt_entries {n : ℕ} (hn : n ∣ m * M') (γ : SL(2, ℤ)) (t : (ZMod (m * M'))ˣ) :
    (((γt γ t) 0 0 : ℤ) : ZMod n) = ((γ 0 0 : ℤ) : ZMod n) ∧
    (((γt γ t) 0 1 : ℤ) : ZMod n) = ZMod.castHom hn (ZMod n) (t : ZMod (m * M')) * ((γ 0 1 : ℤ) : ZMod n) ∧
    (((γt γ t) 1 0 : ℤ) : ZMod n) =
      ZMod.castHom hn (ZMod n) ((t⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) * ((γ 1 0 : ℤ) : ZMod n) ∧
    (((γt γ t) 1 1 : ℤ) : ZMod n) = ((γ 1 1 : ℤ) : ZMod n) := by
  have e00 := congrArg (ZMod.castHom hn (ZMod n)) (γt_red00 (m := m) (M' := M') γ t)
  have e01 := congrArg (ZMod.castHom hn (ZMod n)) (γt_red01 (m := m) (M' := M') γ t)
  have e10 := congrArg (ZMod.castHom hn (ZMod n)) (γt_red10 (m := m) (M' := M') γ t)
  have e11 := congrArg (ZMod.castHom hn (ZMod n)) (γt_red11 (m := m) (M' := M') γ t)
  rw [map_mul] at e01 e10
  simp only [map_intCast] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem castHom_unit_mul_inv {n : ℕ} (hn : n ∣ m * M') (t : (ZMod (m * M'))ˣ) :
    ZMod.castHom hn (ZMod n) (t : ZMod (m * M')) *
      ZMod.castHom hn (ZMod n) ((t⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

end Reps
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section Unit

omit [NeZero m] [NeZero M'] in

theorem mat_two_ext {R : Type*} {A B : Matrix (Fin 2) (Fin 2) R} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  rw [Matrix.eta_fin_two A, Matrix.eta_fin_two B, h00, h01, h10, h11]

omit [NeZero m] [NeZero M'] in

theorem gl_two_ext {R : Type*} [CommRing R] {A B : GL (Fin 2) R}
    (h00 : (A : Matrix (Fin 2) (Fin 2) R) 0 0 = (B : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) R) 0 1 = (B : Matrix (Fin 2) (Fin 2) R) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) R) 1 0 = (B : Matrix (Fin 2) (Fin 2) R) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) R) 1 1 = (B : Matrix (Fin 2) (Fin 2) R) 1 1) : A = B :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    have h := mat_two_ext (A := (A : Matrix (Fin 2) (Fin 2) R)) (B := (B : Matrix (Fin 2) (Fin 2) R)) h00 h01 h10 h11
    rw [h]

omit [NeZero m] [NeZero M'] in

theorem diag_mul_entries {R : Type*} [CommRing R] (s : R) (X : Matrix (Fin 2) (Fin 2) R) :
    (!![(1 : R), 0; 0, s] * X) 0 0 = X 0 0 ∧ (!![(1 : R), 0; 0, s] * X) 0 1 = X 0 1 ∧
    (!![(1 : R), 0; 0, s] * X) 1 0 = s * X 1 0 ∧ (!![(1 : R), 0; 0, s] * X) 1 1 = s * X 1 1 ∧
    (X * !![(1 : R), 0; 0, s]) 0 0 = X 0 0 ∧ (X * !![(1 : R), 0; 0, s]) 0 1 = X 0 1 * s ∧
    (X * !![(1 : R), 0; 0, s]) 1 0 = X 1 0 ∧ (X * !![(1 : R), 0; 0, s]) 1 1 = X 1 1 * s := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (hmM' : Hyp m M' ℓg H₁)
include hmM'

theorem exists_unit_lift {t : ℕ} (ht : Nat.Coprime t m) :
    ∃ u : (ZMod (m * M'))ˣ, ZMod.castHom (dvd_mul_right m M') (ZMod m) (u : ZMod (m * M')) = (t : ZMod m) := by
  obtain ⟨t₀, ht₀m, ht₀M⟩ := Nat.chineseRemainder hmM'.cop t 1
  have hcm : Nat.Coprime t₀ m := by
    have := ht₀m.gcd_eq
    rw [Nat.Coprime, this]; exact ht
  have hcM : Nat.Coprime t₀ M' := by
    have := ht₀M.gcd_eq
    rw [Nat.Coprime, this]; exact Nat.gcd_one_left M'
  refine ⟨ZMod.unitOfCoprime t₀ (Nat.Coprime.mul_right hcm hcM), ?_⟩
  rw [ZMod.coe_unitOfCoprime, map_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht₀m

end Unit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

section Main

variable (hmM' : Hyp m M' ℓg H₁)

theorem γt_cong_mod (γ : SL(2, ℤ)) (u : (ZMod (m * M'))ˣ) (t : ℕ)
    (hu : ZMod.castHom (dvd_mul_right m M') (ZMod m) (u : ZMod (m * M')) = (t : ZMod m)) :
    !![(1 : ZMod m), 0; 0, (t : ZMod m)] * ((γt γ u : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, (t : ZMod m)] := by
  obtain ⟨e00, e01, e10, e11⟩ := γt_entries (m := m) (M' := M') (dvd_mul_right m M') γ u
  have hinv := castHom_unit_mul_inv (m := m) (M' := M') (dvd_mul_right m M') u
  rw [hu] at e01 hinv
  obtain ⟨l00, l01, l10, l11, r00, r01, r10, r11⟩ :=
    diag_mul_entries (t : ZMod m) (((γt γ u : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m))
  obtain ⟨-, -, -, -, s00, s01, s10, s11⟩ :=
    diag_mul_entries (t : ZMod m) ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m))
  refine mat_two_ext ?_ ?_ ?_ ?_
  · rw [l00, s00, Matrix.map_apply, Matrix.map_apply, e00]
  · rw [l01, s01, Matrix.map_apply, Matrix.map_apply, e01, mul_comm]
  · rw [l10, s10, Matrix.map_apply, Matrix.map_apply, e10, ← mul_assoc, hinv, one_mul]
  · rw [l11, s11, Matrix.map_apply, Matrix.map_apply, e11, mul_comm]

omit [NeZero M'] in
theorem q_dvd_mul (q : ℕ) (hqm : q ∣ m) : q ∣ m * M' := dvd_trans hqm (dvd_mul_right m M')

theorem γt_mem_Gamma (q : ℕ) (hqm : q ∣ m) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma q) (u : (ZMod (m * M'))ˣ) :
    γt (m := m) (M' := M') γ u ∈ Gamma q := by
  obtain ⟨e00, e01, e10, e11⟩ := γt_entries (m := m) (M' := M') (q_dvd_mul (M' := M') q hqm) γ u
  rw [Gamma_mem] at hγ ⊢
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, h00]
  · rw [e01, h01, mul_zero]
  · rw [e10, h10, mul_zero]
  · rw [e11, h11]

omit [NeZero m] [NeZero M'] in

theorem redQ_apply (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = ((γ i j : ℤ) : ZMod q) := rfl

theorem redQ_γt (q : ℕ) [Fact q.Prime] (hqm : q ∣ m) (γ : SL(2, ℤ)) (u : (ZMod (m * M'))ˣ) (d : (ZMod q)ˣ)
    (hd : ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = ZMod.castHom (q_dvd_mul (M' := M') q hqm) (ZMod q) (u : ZMod (m * M'))) :
    redQ q (γt (m := m) (M' := M') γ u) = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ := by
  obtain ⟨e00, e01, e10, e11⟩ := γt_entries (m := m) (M' := M') (q_dvd_mul (M' := M') q hqm) γ u
  have hinv := castHom_unit_mul_inv (m := m) (M' := M') (q_dvd_mul (M' := M') q hqm) u
  rw [← hd] at e01 hinv

  have hπ : ZMod.castHom (q_dvd_mul (M' := M') q hqm) (ZMod q) ((u⁻¹ : (ZMod (m * M'))ˣ) : ZMod (m * M')) =
      (d : ZMod q) := by
    have := congrArg (fun z : ZMod q => (d : ZMod q) * z) hinv
    rwa [← mul_assoc, Units.mul_inv, one_mul, mul_one] at this
  rw [hπ] at e10
  rw [eq_mul_inv_iff_mul_eq]
  obtain ⟨-, -, -, -, r00, r01, r10, r11⟩ :=
    diag_mul_entries ((d : ZMod q)) ((redQ q (γt (m := m) (M' := M') γ u) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))
  obtain ⟨l00, l01, l10, l11, -, -, -, -⟩ :=
    diag_mul_entries ((d : ZMod q)) ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))
  have hD : ((diagOneElem q d : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(1 : ZMod q), 0; 0, (d : ZMod q)] :=
    coe_diagOneElem q d
  refine gl_two_ext ?_ ?_ ?_ ?_ <;>
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hD]
  · rw [r00, l00, redQ_apply, redQ_apply, e00]
  · rw [r01, l01, redQ_apply, redQ_apply, e01, mul_comm ((d⁻¹ : (ZMod q)ˣ) : ZMod q), mul_assoc, Units.inv_mul,
      mul_one]
  · rw [r10, l10, redQ_apply, redQ_apply, e10, mul_comm]
  · rw [r11, l11, redQ_apply, redQ_apply, e11, mul_comm]

include hmM'

theorem isLevelAutAt_γt {ξ ξ' : L} (hξ' : IsPrimitiveRoot ξ' m) {t : ℕ} (ht : Nat.Coprime t m) (hξt : ξ ^ t = ξ')
    (u : (ZMod (m * M'))ˣ) (hu : ZMod.castHom (dvd_mul_right m M') (ZMod m) (u : ZMod (m * M')) = (t : ZMod m))
    (K : IntermediateField L (LaurentSeries L)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ : ↥K ≃ₐ[L] ↥K}
    (hτ : IsLevelAutAt L m ξ' m (m ^ 2 * M') H₁ γ K τ) :
    IsLevelAutAt L m ξ m (m ^ 2 * M') H₁ (γt (m := m) (M' := M') γ u) K τ := by
  intro k f g pf pg hf hg hg0 x hx ι hι
  have hγ' : γt (m := m) (M' := M') γ u ∈ Gamma0 M' := γt_mem_Gamma0 hγ u

  have hw₁ : IsPrimitiveRoot (ι ξ') m := hξ'.map_of_injective ι.injective
  have hw₂ : IsPrimitiveRoot (eq m) m := Complex.isPrimitiveRoot_exp m (NeZero.ne m)
  obtain ⟨σ, hσ⟩ := exists_complex_ringEquiv_apply_eq_of_isPrimitiveRoot (mpos m) hw₁ hw₂
  set ι₀ : L →+* ℂ := (σ : ℂ →+* ℂ).comp ι with hι₀
  have hι₀ξ' : ι₀ ξ' = Complex.exp (2 * Real.pi * Complex.I / m) := by
    rw [hι₀, RingHom.comp_apply]; exact hσ

  have hιξ' : ι ξ' = eq m ^ t := by rw [← hξt, map_pow, hι]
  have hσpow : ∀ j : ℕ, (σ : ℂ →+* ℂ) ((eq m ^ t) ^ j) = eq m ^ j := fun j => by
    rw [map_pow, ← hιξ']
    exact congrArg (· ^ j) hσ

  have hV := hτ k f g pf pg hf hg hg0 x hx ι₀ hι₀ξ'
  change coeffMap ι₀ ((τ x : ↥K) : LaurentSeries L) * qC (sl hmM' γ hγ g) = qC (sl hmM' γ hγ f) at hV
  change coeffMap ι ((τ x : ↥K) : LaurentSeries L) * qC (sl hmM' _ hγ' g) = qC (sl hmM' _ hγ' f)
  set W : LaurentSeries ℂ := coeffMap ι ((τ x : ↥K) : LaurentSeries L) with hW
  have hVW : coeffMap ι₀ ((τ x : ↥K) : LaurentSeries L) = coeffMap (σ : ℂ →+* ℂ) W := by
    rw [hW, coeffMap_coeffMap]
  rw [hVW] at hV

  have hg' : g ≠ 0 := ne_zero_of_intSeriesC_ne_zero hg hg0
  have hkk : Even (k + k) := ⟨k, rfl⟩
  have hone : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] := by
    have : !![(1 : ZMod m), 0; 0, ((1 : ℕ) : ZMod m)] = 1 := by
      rw [Nat.cast_one]; exact (Matrix.one_fin_two).symm
    rw [this, one_mul, mul_one]
  have hcong := γt_cong_mod (m := m) (M' := M') γ u t hu
  obtain ⟨hF, hFrat, hFrec⟩ := recip hmM' hkk (f.mul g) (pf * pg) (isIntegralQExp_mul hf hg) γ hγ
  obtain ⟨hG, hGrat, hGrec⟩ := recip hmM' hkk (g.mul g) (pg * pg) (isIntegralQExp_mul hg hg) γ hγ
  have hd11 : (((γt (m := m) (M' := M') γ u) 1 1 : ℤ) : ZMod ℓg) = ((γ 1 1 : ℤ) : ZMod ℓg) := by
    have := congrArg (ZMod.castHom (Dvd.dvd.mul_left hmM'.dvd m) (ZMod ℓg)) (γt_red11 (m := m) (M' := M') γ u)
    rwa [map_intCast, map_intCast] at this
  have hF1 := hFrec 1 γ (Nat.coprime_one_left m) hγ rfl hone
  have hG1 := hGrec 1 γ (Nat.coprime_one_left m) hγ rfl hone
  have hFt := hFrec t _ ht hγ' hd11 hcong
  have hGt := hGrec t _ ht hγ' hd11 hcong
  simp only [pow_one] at hF1 hG1

  have hσF : coeffMap (σ : ℂ →+* ℂ) (qC (sl hmM' _ hγ' (f.mul g))) = qC (sl hmM' γ hγ (f.mul g)) := by
    rw [hFt, hF1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, coeffMap_C, hσpow j, coeffMap_qC_of_ratCast _ (hFrat j)]
  have hσG : coeffMap (σ : ℂ →+* ℂ) (qC (sl hmM' _ hγ' (g.mul g))) = qC (sl hmM' γ hγ (g.mul g)) := by
    rw [hGt, hG1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, coeffMap_C, hσpow j, coeffMap_qC_of_ratCast _ (hGrat j)]

  have hFγ : qC (sl hmM' γ hγ (f.mul g)) = qC (sl hmM' γ hγ f) * qC (sl hmM' γ hγ g) := by
    rw [show qC (sl hmM' γ hγ (f.mul g)) = qC (⇑(sl hmM' γ hγ (f.mul g))) from rfl, sl_mul_apply, qC_mul]
  have hGγ : qC (sl hmM' γ hγ (g.mul g)) = qC (sl hmM' γ hγ g) * qC (sl hmM' γ hγ g) := by
    rw [show qC (sl hmM' γ hγ (g.mul g)) = qC (⇑(sl hmM' γ hγ (g.mul g))) from rfl, sl_mul_apply, qC_mul]
  have hFγ' : qC (sl hmM' _ hγ' (f.mul g)) = qC (sl hmM' _ hγ' f) * qC (sl hmM' _ hγ' g) := by
    rw [show qC (sl hmM' _ hγ' (f.mul g)) = qC (⇑(sl hmM' _ hγ' (f.mul g))) from rfl, sl_mul_apply, qC_mul]
  have hGγ' : qC (sl hmM' _ hγ' (g.mul g)) = qC (sl hmM' _ hγ' g) * qC (sl hmM' _ hγ' g) := by
    rw [show qC (sl hmM' _ hγ' (g.mul g)) = qC (⇑(sl hmM' _ hγ' (g.mul g))) from rfl, sl_mul_apply, qC_mul]

  have hV2 : coeffMap (σ : ℂ →+* ℂ) W * qC (sl hmM' γ hγ (g.mul g)) = qC (sl hmM' γ hγ (f.mul g)) := by
    rw [hGγ, hFγ, ← mul_assoc, hV]

  have hinj := coeffMap_injective_of_complex (σ : ℂ →+* ℂ)
  have hW2 : W * qC (sl hmM' _ hγ' (g.mul g)) = qC (sl hmM' _ hγ' (f.mul g)) := by
    apply hinj
    rw [map_mul, hσG, hσF, hV2]
  rw [hGγ', hFγ', ← mul_assoc] at hW2
  exact mul_right_cancel₀ (qC_sl_ne_zero hmM' _ hγ' hg') hW2

theorem main (q : ℕ) [Fact q.Prime] (hqm : q ∣ m) (ξ ξ' : L) (hξ : IsPrimitiveRoot ξ m) (hξ' : IsPrimitiveRoot ξ' m)
    (K : IntermediateField L (LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L m ξ' m (m ^ 2 * M') (H₁) γ K τ →
        ∃ γ' : SL(2, ℤ),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (H₁) γ' K τ := by

  obtain ⟨t, -, ht, hξt⟩ := (hξ.isPrimitiveRoot_iff).mp hξ'

  obtain ⟨u, hu⟩ := exists_unit_lift (m := m) (M' := M') hmM' ht
  have htq : Nat.Coprime t q := Nat.Coprime.coprime_dvd_right hqm ht
  set d : (ZMod q)ˣ := (ZMod.unitOfCoprime t htq)⁻¹ with hd
  have hdu : ((d⁻¹ : (ZMod q)ˣ) : ZMod q) =
      ZMod.castHom (q_dvd_mul (M' := M') q hqm) (ZMod q) (u : ZMod (m * M')) := by
    rw [hd, inv_inv, ZMod.coe_unitOfCoprime]
    have e : ZMod.castHom hqm (ZMod q) (ZMod.castHom (dvd_mul_right m M') (ZMod m) (u : ZMod (m * M'))) =
        ZMod.castHom (q_dvd_mul (M' := M') q hqm) (ZMod q) (u : ZMod (m * M')) := by
      rw [← RingHom.comp_apply, ZMod.castHom_comp]
    rw [← e, hu, map_natCast]
  refine ⟨d, fun γ hγ τ hτ => ⟨γt γ u, γt_mem_Gamma0 hγ u, fun hΓ => γt_mem_Gamma (m := m) (M' := M') q hqm hΓ u,
    redQ_γt (m := m) (M' := M') q hqm γ u d hdu, ?_⟩⟩
  exact isLevelAutAt_γt (m := m) (M' := M') hmM' hξ' ht hξt u hu K hγ hτ

end Main
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

end W1TW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker.W1TW"

theorem solution
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (ξ ξ' : L) (hξ : IsPrimitiveRoot ξ q) (hξ' : IsPrimitiveRoot ξ' q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L q ξ' q (q ^ 2 * M') H₁ γ K τ →
        ∃ γ' : SL(2, ℤ),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ' K τ :=
  W1TW.main (m := q) (M' := M') (⟨(Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM', hℓgM', hH₁⟩ : W1TW.Hyp q M' ℓg H₁)
    q dvd_rfl ξ ξ' hξ hξ' K

end S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker (solution)
