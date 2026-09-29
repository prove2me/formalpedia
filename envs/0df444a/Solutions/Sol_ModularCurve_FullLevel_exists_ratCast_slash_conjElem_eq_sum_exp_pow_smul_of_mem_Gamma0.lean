-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/df209f64-021b-553e-b7fa-f7cc98abbc45

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1pRR
variable (q : ℕ) [Fact q.Prime]

theorem qpos : 0 < q := (Fact.out : q.Prime).pos
theorem one_lt_q : 1 < q := (Fact.out : q.Prime).one_lt
theorem qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
theorem qneZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
theorem qneC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [qne q])

@[scoped simp] theorem Dr_coe : ((Dr q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, 1] := rfl

theorem det_Dr : ((Dr q).det : ℝ) = q := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

theorem det_Dr_pos : 0 < ((Dr q).det : ℝ) := by
  rw [det_Dr]; exact_mod_cast qpos q

@[scoped simp] theorem conjElem_coe (γ : SL(2, ℤ)) : ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr q * conjElem q γ = (γ : GL (Fin 2) ℝ) * Dr q := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElem_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (qne q), mul_comm]

theorem conjElem_eq (γ : SL(2, ℤ)) : conjElem q γ = (Dr q)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr q := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElem (γ : SL(2, ℤ)) : (conjElem q γ).det = 1 := by
  rw [conjElem_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElem_val (γ : SL(2, ℤ)) : ((conjElem q γ).det : ℝ) = 1 := by
  rw [det_conjElem]; rfl

variable {q}

def upMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, (q : ℤ) * δ 0 1; δ 1 0 / q, δ 1 1]

theorem det_upMat (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) : (upMat (q := q) δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (q : ℤ) * c / q = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (qneZ q)
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def upSL (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨upMat (q := q) δ, det_upMat δ h⟩

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / q; (q : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : (downMat (q := q) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (q := q) ε, det_downMat ε h⟩

theorem upSL_coe (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) :
    ((upSL δ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr q = Dr q * (δ : GL (Fin 2) ℝ) := by
  obtain ⟨c, hc⟩ := h
  have h1 : (q : ℤ) * c / q = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (qneZ q)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upSL, upMat, hc, h1] <;> ring

theorem downSL_coe (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) :
    Dr q * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr q := by
  obtain ⟨b, hb⟩ := h
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

theorem downSL_eq (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) :
    ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr q)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr q := by
  rw [mul_assoc, ← downSL_coe ε h, inv_mul_cancel_left]

end W1pRR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

namespace W1pRR
variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M')

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH q M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev GamR : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma (q * M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {q M'}

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH q M' ↔ ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

abbrev SLq (q : ℕ) : SL(2, ℤ) →* SL(2, ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))

theorem SLq_apply (A : SL(2, ℤ)) (i j : Fin 2) : (SLq q A) i j = ((A i j : ℤ) : ZMod q) := by
  simp

omit [Fact q.Prime] in
theorem q_dvd_level : (q : ℤ) ∣ ((q ^ 2 * M' : ℕ) : ℤ) := ⟨q * M', by push_cast; ring⟩

theorem SLq_eq_one_iff (A : SL(2, ℤ)) : SLq q A = 1 ↔
    ((A 0 0 : ℤ) : ZMod q) = 1 ∧ ((A 0 1 : ℤ) : ZMod q) = 0 ∧ ((A 1 0 : ℤ) : ZMod q) = 0 ∧
      ((A 1 1 : ℤ) : ZMod q) = 1 := by
  constructor
  · intro h
    have e : ∀ i j, ((A i j : ℤ) : ZMod q) = (1 : SL(2, ZMod q)) i j := fun i j => by
      rw [← SLq_apply, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e]
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    rw [SLq_apply]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem SLq_eq_iff (A B : SL(2, ℤ)) : SLq q A = SLq q B ↔ ∀ i j, ((A i j : ℤ) : ZMod q) = ((B i j : ℤ) : ZMod q) := by
  constructor
  · intro h i j
    rw [← SLq_apply, ← SLq_apply, h]
  · intro h
    ext i j
    rw [SLq_apply, SLq_apply, h]

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') : ((δ 0 0 : ℤ) : ZMod q) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') : (q : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    SLq q (upSL δ (q_dvd_lowerLeft_of_mem_GH hδ)) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod q) = 1
    exact upperLeft_of_mem_GH hδ
  · show (((q : ℤ) * δ 0 1 : ℤ) : ZMod q) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / q : ℤ) : ZMod q) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (q : ℤ) ^ 2 * M' * c = q * (q * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (qneZ q)]
  · show ((δ 1 1 : ℤ) : ZMod q) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / q : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨q * c, ?_⟩
  push_cast
  rw [show (q : ℤ) ^ 2 * M' * c = q * (M' * (q * c)) by ring, Int.mul_ediv_cancel_left _ (qneZ q)]

theorem intCast_zmod_of_dvd {a b : ℕ} (h : a ∣ b) {x : ℤ} {y : ℤ} (hxy : ((x : ℤ) : ZMod b) = (y : ZMod b)) :
    ((x : ℤ) : ZMod a) = (y : ZMod a) := by
  have := congrArg (ZMod.castHom h (ZMod a)) hxy
  rwa [map_intCast, map_intCast] at this

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem isCoprime_q_M' : IsCoprime (q : ℤ) (M' : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM'

theorem coprime_q_M' : Nat.Coprime q M' :=
  (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM'

omit [Fact q.Prime] in
theorem M'_ne_zero : M' ≠ 0 := by
  rintro rfl; exact hqM' (dvd_zero q)

theorem downSL_mem_GH {ε : SL(2, ℤ)} (hε : SLq q ε = 1) (hM : (M' : ℤ) ∣ ε 1 0) :
    ∃ h01 : (q : ℤ) ∣ ε 0 1, downSL ε h01 ∈ GH q M' := by
  obtain ⟨_, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hε
  have h01 : (q : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨h01, ?_⟩
  rw [mem_GH_iff]
  refine ⟨?_, e11⟩
  show (((q : ℤ) * ε 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (q : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
  obtain ⟨c, hc⟩ := (isCoprime_q_M' hqM').mul_dvd hq hM
  refine ⟨c, ?_⟩
  rw [hc]; push_cast; ring

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    ∃ δ' ∈ GH q M', ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElem q γ * (δ : GL (Fin 2) ℝ) * (conjElem q γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq q ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hδ, mul_one, map_inv, mul_inv_cancel]
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hδ)) (inv_mem hγ)
  have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
  obtain ⟨h01, hmem⟩ := downSL_mem_GH hqM' hεq hM
  refine ⟨downSL ε h01, hmem, ?_⟩
  have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hδ)
  rw [← hu] at hup
  have e2 : (u : GL (Fin 2) ℝ) = Dr q * (δ : GL (Fin 2) ℝ) * (Dr q)⁻¹ := by
    rw [← hup, mul_inv_cancel_right]
  rw [downSL_eq, hε]
  simp only [map_mul, map_inv]
  rw [e2, conjElem_eq]
  group

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ q M' ≤ ConjAct.toConjAct (conjElem q γ)⁻¹ • Γ q M' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hqM' hγ hδ
  exact ⟨δ', hδ', e⟩

theorem Gamma_le_conj : GamR q M' ≤ ConjAct.toConjAct ((Dr q)⁻¹)⁻¹ • Γ q M' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, inv_inv]
  rw [SetLike.mem_coe, Gamma_mem] at hδ
  obtain ⟨e00, e01, e10, e11⟩ := hδ
  have hq : q ∣ q * M' := dvd_mul_right q M'
  have hM'd : M' ∣ q * M' := dvd_mul_left M' q
  have hεq : SLq q δ = 1 := by
    rw [SLq_eq_one_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := intCast_zmod_of_dvd hq (y := 1) (by exact_mod_cast e00); exact_mod_cast this
    · have := intCast_zmod_of_dvd hq (y := 0) (by exact_mod_cast e01); exact_mod_cast this
    · have := intCast_zmod_of_dvd hq (y := 0) (by exact_mod_cast e10); exact_mod_cast this
    · have := intCast_zmod_of_dvd hq (y := 1) (by exact_mod_cast e11); exact_mod_cast this
  have hM : (M' : ℤ) ∣ δ 1 0 := by
    have := intCast_zmod_of_dvd hM'd (y := 0) (by exact_mod_cast e10)
    rw [Int.cast_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨h01, hmem⟩ := downSL_mem_GH hqM' hεq hM
  exact ⟨downSL δ h01, hmem, downSL_eq δ h01⟩

theorem exists_conjElem_eq_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M') (h₂ : γ₂ ∈ Gamma0 M')
    (h : SLq q γ₁ = SLq q γ₂) :
    ∃ δ ∈ GH q M', conjElem q γ₁ = ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * conjElem q γ₂ := by
  set ε : SL(2, ℤ) := γ₁ * γ₂⁻¹ with hε
  have hεq : SLq q ε = 1 := by rw [hε, map_mul, map_inv, h, mul_inv_cancel]
  have hε0 : ε ∈ Gamma0 M' := mul_mem h₁ (inv_mem h₂)
  have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
  obtain ⟨h01, hmem⟩ := downSL_mem_GH hqM' hεq hM
  refine ⟨downSL ε h01, hmem, ?_⟩
  rw [downSL_eq, conjElem_eq, conjElem_eq, hε]
  simp only [map_mul, map_inv]
  group

end W1pRR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

namespace W1pRR

open UpperHalfPlane Complex Function
open scoped ModularForm Real Manifold Topology

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

omit [Fact q.Prime] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ q M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

omit [Fact q.Prime] in
theorem natCast_mem_strictPeriods (n : ℕ) : (n : ℝ) ∈ (Γ q M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _),
    AddSubgroup.mem_zmultiples_iff]
  exact ⟨n, by simp⟩

omit [Fact q.Prime] in
theorem level_mem_strictPeriods_GamR : ((q * M' : ℕ) : ℝ) ∈ (GamR q M').strictPeriods := by
  rw [GamR, CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

section Slash

variable (hqM' : ¬ q ∣ M')
include hqM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    ModularForm (Γ q M') k :=
  restrictForm (le_conj hqM' hγ) (ModularForm.translate f (conjElem q γ))

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    ⇑(sl hqM' γ hγ f) = ⇑f ∣[k] conjElem q γ := rfl

theorem slash_conjElem_eq_of_SLq_eq {k : ℤ} (f : ModularForm (Γ q M') k) {γ₁ γ₂ : SL(2, ℤ)}
    (h₁ : γ₁ ∈ Gamma0 M') (h₂ : γ₂ ∈ Gamma0 M') (h : SLq q γ₁ = SLq q γ₂) :
    (⇑f : ℍ → ℂ) ∣[k] conjElem q γ₁ = (⇑f : ℍ → ℂ) ∣[k] conjElem q γ₂ := by
  obtain ⟨δ, hδ, e⟩ := exists_conjElem_eq_mul hqM' h₁ h₂ h
  rw [e, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hδ)

def FF {k : ℤ} (f : ModularForm (Γ q M') k) : ModularForm (GamR q M') k :=
  restrictForm (Gamma_le_conj hqM') (ModularForm.translate f (Dr q)⁻¹)

@[scoped simp]
theorem coe_FF {k : ℤ} (f : ModularForm (Γ q M') k) : ⇑(FF hqM' f) = ⇑f ∣[k] (Dr q)⁻¹ := rfl

theorem slash_conjElem_eq_FF {k : ℤ} (f : ModularForm (Γ q M') k) (γ : SL(2, ℤ)) :
    (⇑f : ℍ → ℂ) ∣[k] conjElem q γ = ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] Dr q := by
  rw [coe_FF, conjElem_eq, SlashAction.slash_mul, SlashAction.slash_mul]

theorem FF_slash_eq {k : ℤ} (f : ModularForm (Γ q M') k) (γ : SL(2, ℤ)) :
    (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = ((⇑f : ℍ → ℂ) ∣[k] conjElem q γ) ∣[k] (Dr q)⁻¹ := by
  rw [slash_conjElem_eq_FF, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

theorem σ_Dr : UpperHalfPlane.σ (Dr q) = ContinuousAlgEquiv.refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_Dr_pos q)]

theorem denom_Dr (τ : ℍ) : denom (Dr q) (τ : ℂ) = 1 := by
  simp [denom, Dr_coe]

theorem coe_Dr_smul (τ : ℍ) : ((Dr q • τ : ℍ) : ℂ) = (q : ℂ) * (τ : ℂ) := by
  rw [coe_smul_of_det_pos (det_Dr_pos q)]
  simp [num, denom, Dr_coe]

theorem slash_Dr_apply {k : ℤ} (φ : ℍ → ℂ) (τ : ℍ) :
    (φ ∣[k] Dr q) τ = (q : ℂ) ^ (k - 1) * φ (Dr q • τ) := by
  rw [ModularForm.slash_apply, σ_Dr, det_Dr, denom_Dr, _root_.one_zpow, mul_one,
    abs_of_pos (by exact_mod_cast qpos q : (0 : ℝ) < q), Complex.ofReal_natCast, mul_comm]
  rfl

theorem coe_Dr_inv_smul (τ : ℍ) : (((Dr q)⁻¹ • τ : ℍ) : ℂ) = (τ : ℂ) / q := by
  have h := coe_Dr_smul (q := q) ((Dr q)⁻¹ • τ)
  rw [smul_smul, mul_inv_cancel, one_smul] at h
  rw [h, mul_div_cancel_left₀ _ (qneC q)]

section QExp

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem qParam_one_eq_pow (L : ℕ) [NeZero L] (τ : ℍ) :
    Periodic.qParam 1 τ = Periodic.qParam L τ ^ L := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  push_cast
  field_simp

theorem qExpansion_coeff_widthN (L : ℕ) [NeZero L] {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion L g).coeff n = if (L : ℕ) ∣ n then (qExpansion 1 g).coeff (n / L) else 0 := by
  classical
  have hLpos' : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hperN : Periodic (g ∘ ofComplex) L := by simpa using hper.nat_mul L
  set c : ℕ → ℂ := fun n => if (L : ℕ) ∣ n then (qExpansion 1 g).coeff (n / L) else 0 with hc
  have hLpos : 0 < L := NeZero.pos L
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam L τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => L * m := mul_right_injective₀ hLpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => L * m),
        (fun m => c m • Periodic.qParam L τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (L : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [Function.comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hLpos]
    rw [qParam_one_eq_pow L τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' hLpos' (analyticAt_cuspFunction_zero hLpos' hperN hg hbd) hsum n]

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem levelN_pos : (0 : ℝ) < ((q * M' : ℕ) : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero (Fact.out : q.Prime).ne_zero (M'_ne_zero hqM')))

theorem neZero_levelN : NeZero (q * M') := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (M'_ne_zero hqM')⟩

theorem FF_slash_Dr {k : ℤ} (f : ModularForm (Γ q M') k) : (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] Dr q = ⇑f := by
  rw [coe_FF, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem FF_apply {k : ℤ} (f : ModularForm (Γ q M') k) (τ : ℍ) :
    FF hqM' f τ = ((q : ℂ) ^ (k - 1))⁻¹ * f ((Dr q)⁻¹ • τ) := by
  have h := congrFun (FF_slash_Dr hqM' f) ((Dr q)⁻¹ • τ)
  rw [slash_Dr_apply, smul_smul, mul_inv_cancel, one_smul] at h
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ (qneC q)), one_mul]

theorem qParam_one_Dr_inv_smul (τ : ℍ) :
    Periodic.qParam 1 (((Dr q)⁻¹ • τ : ℍ) : ℂ) = Periodic.qParam ((q * M' : ℕ) : ℝ) τ ^ M' := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul, coe_Dr_inv_smul]
  congr 1
  have hM : (M' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (M'_ne_zero hqM')
  push_cast
  field_simp [qneC q]

theorem qParam_levelN_Dr_smul (τ : ℍ) :
    Periodic.qParam ((q * M' : ℕ) : ℝ) ((Dr q • τ : ℍ) : ℂ) = Periodic.qParam (M' : ℝ) τ := by
  simp only [Periodic.qParam]
  rw [coe_Dr_smul]
  congr 1
  have hM : (M' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (M'_ne_zero hqM')
  push_cast
  field_simp [qneC q]

scoped instance fact_isCusp : Fact (IsCusp OnePoint.infty (Γ q M')) :=
  ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩

theorem exists_ratCast_qExpansion_FF {k : ℤ} (f : ModularForm (Γ q M') k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ)) (m : ℕ) :
    ∃ r : ℚ, (qExpansion ((q * M' : ℕ) : ℝ) (FF hqM' f)).coeff m = (r : ℂ) := by
  classical
  have hM'pos : 0 < M' := Nat.pos_of_ne_zero (M'_ne_zero hqM')
  set a : ℕ → ℂ := fun n => (qExpansion 1 f).coeff n with ha
  set c : ℕ → ℂ := fun m => if M' ∣ m then ((q : ℂ) ^ (k - 1))⁻¹ * a (m / M') else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam ((q * M' : ℕ) : ℝ) τ ^ m) (FF hqM' f τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
      f.holo' (ModularFormClass.bdd_at_infty f) ((Dr q)⁻¹ • τ)
    have h2 := h1.mul_left (((q : ℂ) ^ (k - 1))⁻¹)
    rw [← FF_apply hqM' f τ] at h2
    have hinj : Function.Injective fun n : ℕ => M' * n := mul_right_injective₀ hM'pos.ne'
    have hsupp : ∀ x ∉ Set.range (fun n : ℕ => M' * n),
        (fun m => c m • Periodic.qParam ((q * M' : ℕ) : ℝ) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ M' ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    funext n
    simp only [Function.comp_apply, hc, ha, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hM'pos, smul_eq_mul]
    rw [qParam_one_Dr_inv_smul hqM' τ, ← pow_mul]
    ring
  have hcoef := ModularFormClass.qExpansion_coeff_unique (levelN_pos hqM') level_mem_strictPeriods_GamR
    (f := FF hqM' f) hsum m
  rw [← hcoef, hc]
  simp only
  split_ifs with hd
  · obtain ⟨r, hr⟩ := hf (m / M')
    refine ⟨((q : ℚ) ^ (k - 1))⁻¹ * r, ?_⟩
    rw [ha]; simp only; rw [hr]; push_cast; ring
  · exact ⟨0, by simp⟩

theorem coeff_qExpansion_sl {k : ℤ} (f : ModularForm (Γ q M') k) {γ₁ : SL(2, ℤ)} (hγ₁ : γ₁ ∈ Gamma0 M')
    (G : ModularForm (GamR q M') k) (hG : (⇑G : ℍ → ℂ) = (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γ₁ : GL (Fin 2) ℝ))
    (n : ℕ) :
    (qExpansion 1 (sl hqM' γ₁ hγ₁ f)).coeff n =
      (q : ℂ) ^ (k - 1) * (qExpansion ((q * M' : ℕ) : ℝ) G).coeff (M' * n) := by
  have hM'pos : 0 < M' := Nat.pos_of_ne_zero (M'_ne_zero hqM')
  haveI : NeZero M' := ⟨(M'_ne_zero hqM')⟩
  have hM'posR : (0 : ℝ) < M' := Nat.cast_pos.mpr hM'pos
  set g := sl hqM' γ₁ hγ₁ f with hg

  have hgG : ∀ τ : ℍ, g τ = (q : ℂ) ^ (k - 1) * G (Dr q • τ) := by
    intro τ
    have : (⇑g : ℍ → ℂ) = (⇑G : ℍ → ℂ) ∣[k] Dr q := by
      rw [hg, coe_sl, slash_conjElem_eq_FF hqM', hG]
    rw [this, slash_Dr_apply]

  set C : ℕ → ℂ := fun m => (qExpansion ((q * M' : ℕ) : ℝ) G).coeff m with hC
  have hsum : ∀ τ : ℍ, HasSum (fun m => ((q : ℂ) ^ (k - 1) * C m) • Periodic.qParam (M' : ℝ) τ ^ m) (g τ) := by
    intro τ
    haveI : Fact (IsCusp OnePoint.infty (GamR q M')) :=
      ⟨Subgroup.isCusp_of_mem_strictPeriods (levelN_pos hqM') level_mem_strictPeriods_GamR⟩
    have h1 := hasSum_qExpansion (levelN_pos hqM')
      (SlashInvariantFormClass.periodic_comp_ofComplex G level_mem_strictPeriods_GamR)
      G.holo' (ModularFormClass.bdd_at_infty G) (Dr q • τ)
    have h2 := h1.mul_left ((q : ℂ) ^ (k - 1))
    rw [← hgG τ] at h2
    convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    funext m
    simp only [hC, smul_eq_mul, qParam_levelN_Dr_smul hqM' τ]
    ring
  have hcoefM := ModularFormClass.qExpansion_coeff_unique hM'posR (natCast_mem_strictPeriods M') (f := g)
    hsum (M' * n)

  have hwid := qExpansion_coeff_widthN M' (ModularFormClass.holo g)
    (SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods) (ModularFormClass.bdd_at_infty g)
    (M' * n)
  rw [if_pos (dvd_mul_right M' n), Nat.mul_div_cancel_left _ hM'pos] at hwid
  rw [← hwid, ← hcoefM]

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

section Cyclo

variable (L : ℕ) [NeZero L]

def zetaC : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaC L}

omit [NeZero L] in
theorem kN_eq : kN L = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))} := rfl

theorem isPrimitiveRoot_zetaC : IsPrimitiveRoot (zetaC L) L :=
  Complex.isPrimitiveRoot_exp L (NeZero.ne L)

scoped instance instIsCyclotomic : IsCyclotomicExtension {L} ℚ (kN L) := by
  have hζ := isPrimitiveRoot_zetaC L
  change IsCyclotomicExtension {L} ℚ (IntermediateField.adjoin ℚ {zetaC L}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos L)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

scoped instance instIsGalois : IsGalois ℚ (kN L) := IsCyclotomicExtension.isGalois {L} ℚ (kN L)

scoped instance instFiniteDimensional : FiniteDimensional ℚ (kN L) :=
  IsCyclotomicExtension.finiteDimensional {L} ℚ (kN L)

def zetaK : kN L := ⟨zetaC L, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

omit [NeZero L] in
@[scoped simp] theorem coe_zetaK : ((zetaK L : kN L) : ℂ) = zetaC L := rfl

theorem isPrimitiveRoot_zetaK : IsPrimitiveRoot (zetaK L) L := by
  have h := isPrimitiveRoot_zetaC L
  rw [← coe_zetaK] at h
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h

theorem exists_rat_of_fixed (x : kN L) (hx : ∀ σ : (kN L) ≃ₐ[ℚ] (kN L), σ x = x) :
    ∃ r : ℚ, (x : ℂ) = (r : ℂ) := by
  have := (IsGalois.mem_bot_iff_fixed x).2 hx
  rw [IntermediateField.mem_bot] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨r, ?_⟩
  rw [← hr]
  rfl

omit [NeZero L] in
theorem coe_algebraMap_rat (r : ℚ) : ((algebraMap ℚ (kN L) r : kN L) : ℂ) = (r : ℂ) := by
  have : ((algebraMap ℚ (kN L) r : kN L) : ℂ) = ((algebraMap (kN L) ℂ).comp (algebraMap ℚ (kN L))) r := rfl
  rw [this, eq_ratCast]

def phiOf (σ : (kN L) ≃ₐ[ℚ] (kN L)) : kN L →+* ℂ :=
  (algebraMap (kN L) ℂ).comp σ.toRingEquiv.toRingHom

omit [NeZero L] in
theorem phiOf_apply (σ : (kN L) ≃ₐ[ℚ] (kN L)) (z : kN L) : phiOf L σ z = ((σ z : kN L) : ℂ) := rfl

omit [NeZero L] in
theorem phiOf_spec (σ : (kN L) ≃ₐ[ℚ] (kN L)) {t : ℕ} (hσ : σ (zetaK L) = zetaK L ^ t) :
    ∀ z : kN L, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ)) →
      phiOf L σ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ)) ^ t := by
  intro z hz
  have : z = zetaK L := Subtype.ext hz
  rw [phiOf_apply, this, hσ]
  rfl

theorem exists_aut_pow_eq (t : ℕ) (ht : t.Coprime L) :
    ∃ σ : (kN L) ≃ₐ[ℚ] (kN L), σ (zetaK L) = zetaK L ^ t := by
  have hζ := isPrimitiveRoot_zetaK L
  have hirr : Irreducible (Polynomial.cyclotomic L ℚ) := Polynomial.cyclotomic.irreducible_rat (NeZero.pos L)
  have hμ : IsPrimitiveRoot (zetaK L ^ t) L := hζ.pow_of_coprime t ht
  have h1 := hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  have h2 := hμ.minpoly_eq_cyclotomic_of_irreducible hirr
  have hmin : minpoly ℚ (hζ.powerBasis ℚ).gen = minpoly ℚ (hμ.powerBasis ℚ).gen := by
    rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen, ← h1, ← h2]
  refine ⟨(hζ.powerBasis ℚ).equivOfMinpoly (hμ.powerBasis ℚ) hmin, ?_⟩
  have := (hζ.powerBasis ℚ).equivOfMinpoly_gen (hμ.powerBasis ℚ) hmin
  rwa [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen] at this

theorem aut_zetaK (σ : (kN L) ≃ₐ[ℚ] (kN L)) :
    σ (zetaK L) = zetaK L ^ (((isPrimitiveRoot_zetaK L).autToPow ℚ σ : (ZMod L)ˣ) : ZMod L).val :=
  ((isPrimitiveRoot_zetaK L).autToPow_spec ℚ σ).symm

theorem zetaK_pow_mod (x : ℕ) : zetaK L ^ (x % L) = zetaK L ^ x := by
  conv_rhs => rw [← Nat.mod_add_div x L, pow_add, pow_mul, (isPrimitiveRoot_zetaK L).pow_eq_one, one_pow,
    mul_one]

end Cyclo
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

section Reps

variable [NeZero M']

def liftSL (X : SL(2, ZMod (q * M'))) : SL(2, ℤ) :=
  Classical.choose (ModularCurve.surjective_specialLinearGroup_map_zmod (q * M') X)

theorem liftSL_spec (X : SL(2, ZMod (q * M'))) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * M'))) (liftSL X) = X :=
  Classical.choose_spec (ModularCurve.surjective_specialLinearGroup_map_zmod (q * M') X)

theorem liftSL_entry (X : SL(2, ZMod (q * M'))) (i j : Fin 2) :
    (((liftSL X) i j : ℤ) : ZMod (q * M')) = X i j := by
  have := congrArg (fun Y : SL(2, ZMod (q * M')) => Y i j) (liftSL_spec X)
  simpa using this

def red (γ : SL(2, ℤ)) (i j : Fin 2) : ZMod (q * M') := ((γ i j : ℤ) : ZMod (q * M'))

omit [NeZero M'] in
theorem red_apply (γ : SL(2, ℤ)) (i j : Fin 2) : red (q := q) (M' := M') γ i j = ((γ i j : ℤ) : ZMod (q * M')) :=
  rfl

omit [NeZero M'] in
theorem red_det (γ : SL(2, ℤ)) : red (q := q) (M' := M') γ 0 0 * red γ 1 1 - red γ 0 1 * red γ 1 0 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod (q * M'))) hdet
  push_cast at this
  exact this

def Xt (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) : SL(2, ZMod (q * M')) :=
  ⟨!![red γ 0 0, (t : ZMod (q * M')) * red γ 0 1; ((t⁻¹ : (ZMod (q * M'))ˣ) : ZMod (q * M')) * red γ 1 0, red γ 1 1],
    by
      rw [Matrix.det_fin_two_of]
      have h := red_det (q := q) (M' := M') γ
      have ht : (t : ZMod (q * M')) * ((t⁻¹ : (ZMod (q * M'))ˣ) : ZMod (q * M')) = 1 := Units.mul_inv t
      linear_combination h - (red γ 0 1 * red γ 1 0) * ht⟩

def γt (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) : SL(2, ℤ) := liftSL (Xt γ t)

theorem γt_red (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) (i j : Fin 2) :
    (((γt γ t) i j : ℤ) : ZMod (q * M')) = Xt γ t i j :=
  liftSL_entry (Xt γ t) i j

theorem γt_red00 (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    (((γt γ t) 0 0 : ℤ) : ZMod (q * M')) = ((γ 0 0 : ℤ) : ZMod (q * M')) := by
  rw [γt_red]; rfl
theorem γt_red01 (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    (((γt γ t) 0 1 : ℤ) : ZMod (q * M')) = (t : ZMod (q * M')) * ((γ 0 1 : ℤ) : ZMod (q * M')) := by
  rw [γt_red]; rfl
theorem γt_red10 (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    (((γt γ t) 1 0 : ℤ) : ZMod (q * M')) = ((t⁻¹ : (ZMod (q * M'))ˣ) : ZMod (q * M')) * ((γ 1 0 : ℤ) : ZMod (q * M')) := by
  rw [γt_red]; rfl
theorem γt_red11 (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    (((γt γ t) 1 1 : ℤ) : ZMod (q * M')) = ((γ 1 1 : ℤ) : ZMod (q * M')) := by
  rw [γt_red]; rfl

theorem γt_cong (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    !![(1 : ZMod (q * M')), 0; 0, (((t : ZMod (q * M')).val : ℕ) : ZMod (q * M'))] *
        ((γt γ t : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (q * M'))
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (q * M')) *
        !![(1 : ZMod (q * M')), 0; 0, (((t : ZMod (q * M')).val : ℕ) : ZMod (q * M'))] := by
  rw [ZMod.natCast_zmod_val]
  have e00 := γt_red00 (q := q) (M' := M') γ t
  have e01 := γt_red01 (q := q) (M' := M') γ t
  have e10 := γt_red10 (q := q) (M' := M') γ t
  have e11 := γt_red11 (q := q) (M' := M') γ t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, e00, e01, e10, e11, mul_comm]

theorem γt_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (t : (ZMod (q * M'))ˣ) : γt (q := q) γ t ∈ Gamma0 M' := by
  rw [Gamma0_mem] at hγ ⊢
  have h := γt_red10 (q := q) (M' := M') γ t
  have := congrArg (ZMod.castHom (dvd_mul_left M' q) (ZMod M')) h
  rw [map_intCast, map_mul, map_intCast, hγ, mul_zero] at this
  exact this

abbrev ured (t : (ZMod (q * M'))ˣ) : (ZMod q)ˣ := ZMod.unitsMap (dvd_mul_right q M') t

omit [NeZero M'] in
theorem coe_ured (t : (ZMod (q * M'))ˣ) :
    ((ured t : (ZMod q)ˣ) : ZMod q) = ZMod.castHom (dvd_mul_right q M') (ZMod q) (t : ZMod (q * M')) := by
  simp [ured, ZMod.unitsMap_def]

omit [NeZero M'] in
theorem coe_ured_inv (t : (ZMod (q * M'))ˣ) :
    (((ured t)⁻¹ : (ZMod q)ˣ) : ZMod q) =
      ZMod.castHom (dvd_mul_right q M') (ZMod q) ((t⁻¹ : (ZMod (q * M'))ˣ) : ZMod (q * M')) := by
  rw [ured, ZMod.unitsMap_def, Units.coe_map_inv]
  rfl

def Yq (γ : SL(2, ℤ)) (u : (ZMod q)ˣ) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![((γ 0 0 : ℤ) : ZMod q), (u : ZMod q) * ((γ 0 1 : ℤ) : ZMod q);
     ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((γ 1 0 : ℤ) : ZMod q), ((γ 1 1 : ℤ) : ZMod q)]

omit [NeZero M'] in
theorem red_castHom (γ : SL(2, ℤ)) (i j : Fin 2) :
    ZMod.castHom (dvd_mul_right q M') (ZMod q) ((γ i j : ℤ) : ZMod (q * M')) = ((γ i j : ℤ) : ZMod q) := by
  rw [map_intCast]

theorem SLq_γt (γ : SL(2, ℤ)) (t : (ZMod (q * M'))ˣ) :
    ((SLq q (γt γ t) : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = Yq γ (ured t) := by
  have e00 := congrArg (ZMod.castHom (dvd_mul_right q M') (ZMod q)) (γt_red00 (q := q) (M' := M') γ t)
  have e01 := congrArg (ZMod.castHom (dvd_mul_right q M') (ZMod q)) (γt_red01 (q := q) (M' := M') γ t)
  have e10 := congrArg (ZMod.castHom (dvd_mul_right q M') (ZMod q)) (γt_red10 (q := q) (M' := M') γ t)
  have e11 := congrArg (ZMod.castHom (dvd_mul_right q M') (ZMod q)) (γt_red11 (q := q) (M' := M') γ t)
  rw [map_mul] at e01 e10
  simp only [red_castHom (q := q) (M' := M')] at e00 e01 e10 e11
  rw [← coe_ured] at e01
  rw [← coe_ured_inv] at e10
  ext i j
  rw [SLq_apply]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

omit [NeZero M'] in

theorem SLq_eq_Yq_of_hyp (γ γ' : SL(2, ℤ)) (s : ℕ) (hs : s.Coprime q)
    (h : !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)]) :
    ((SLq q γ' : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = Yq γ (ZMod.unitOfCoprime s hs) := by
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime s hs with hu
  have hsu : (s : ZMod q) = (u : ZMod q) := (ZMod.coe_unitOfCoprime s hs).symm
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero,
    zero_add, mul_one, mul_zero] at h00 h01 h10 h11
  rw [hsu] at h10 h11 h01
  ext i j
  rw [SLq_apply]
  fin_cases i <;> fin_cases j
  · exact h00
  · show ((γ' 0 1 : ℤ) : ZMod q) = (u : ZMod q) * ((γ 0 1 : ℤ) : ZMod q)
    rw [h01, mul_comm]
  · show ((γ' 1 0 : ℤ) : ZMod q) = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((γ 1 0 : ℤ) : ZMod q)
    rw [← h10, ← mul_assoc, Units.inv_mul, one_mul]
  · show ((γ' 1 1 : ℤ) : ZMod q) = ((γ 1 1 : ℤ) : ZMod q)
    exact Units.mul_right_inj u |>.mp (h11.trans (mul_comm _ _))

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem slash_conjElem_γt_eq_of_ured_eq {k : ℤ} (f : ModularForm (Γ q M') k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M')
    {t t' : (ZMod (q * M'))ˣ} (h : ured t = ured t') :
    (⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ t) = (⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ t') :=
  slash_conjElem_eq_of_SLq_eq hqM' f (γt_mem_Gamma0 hγ t) (γt_mem_Gamma0 hγ t')
    (Subtype.ext (by rw [SLq_γt, SLq_γt, h]))

theorem slash_conjElem_eq_γt {k : ℤ} (f : ModularForm (Γ q M') k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M')
    {s : ℕ} {γ' : SL(2, ℤ)} (hs : s.Coprime q) (hγ' : γ' ∈ Gamma0 M')
    (h : !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)])
    {t : (ZMod (q * M'))ˣ} (ht : ured t = ZMod.unitOfCoprime s hs) :
    (⇑f : ℍ → ℂ) ∣[k] conjElem q γ' = (⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ t) :=
  slash_conjElem_eq_of_SLq_eq hqM' f hγ' (γt_mem_Gamma0 hγ t)
    (Subtype.ext (by rw [SLq_eq_Yq_of_hyp γ γ' s hs h, SLq_γt, ht]))

end Reps
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

section Recip

variable [NeZero M']

def slashSL {k : ℤ} (α : SL(2, ℤ)) (F : ModularForm (GamR q M') k) : ModularForm (GamR q M') k where
  toFun := (⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : α * A * α⁻¹ ∈ CongruenceSubgroup.Gamma (q * M') :=
      (CongruenceSubgroup.Gamma_normal (q * M')).conj_mem A hA α
    have hGL : (α : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((α * A * α⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (α : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    change ((⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := F.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (GamR q M')).mp hc
    have hc' : IsCusp ((α : GL (Fin 2) ℝ) • c) (GamR q M') := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨α, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (F.bdd_at_cusps' hc')

theorem coe_slashSL {k : ℤ} (α : SL(2, ℤ)) (F : ModularForm (GamR q M') k) :
    (⇑(slashSL α F) : ℍ → ℂ) = (⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ) := rfl

variable (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k) (f : ModularForm (Γ q M') k)
  (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ)) (γ : SL(2, ℤ))
include hqM' hk hf

theorem key_recip (t : (ZMod (q * M'))ˣ) (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M')))
    (hσ : σ (zetaK (q * M')) = zetaK (q * M') ^ ((t : ZMod (q * M'))).val) (m : ℕ) :
    ∃ z : kN (q * M'), (z : ℂ) = (qExpansion ((q * M' : ℕ) : ℝ) ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] γ)).coeff m ∧
      (qExpansion ((q * M' : ℕ) : ℝ) ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ t))).coeff m = phiOf (q * M') σ z :=
  ModularCurve.exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even (q * M') hk (FF hqM' f)
    (exists_ratCast_qExpansion_FF hqM' f hf) (kN (q * M')) (kN_eq (q * M')) ((t : ZMod (q * M'))).val
    (ZMod.val_coe_unit_coprime t) (phiOf (q * M') σ) (phiOf_spec (q * M') σ hσ) γ (γt γ t) (γt_cong γ t) m

theorem exists_zc (m : ℕ) : ∃ z : kN (q * M'),
    (z : ℂ) = (qExpansion ((q * M' : ℕ) : ℝ) ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] γ)).coeff m := by
  obtain ⟨σ, hσ⟩ := exists_aut_pow_eq (q * M') (((1 : (ZMod (q * M'))ˣ) : ZMod (q * M'))).val
    (ZMod.val_coe_unit_coprime 1)
  obtain ⟨z, hz, -⟩ := key_recip hqM' hk f hf γ 1 σ hσ m
  exact ⟨z, hz⟩

def zc (m : ℕ) : kN (q * M') := Classical.choose (exists_zc hqM' hk f hf γ m)

theorem zc_spec (m : ℕ) :
    ((zc hqM' hk f hf γ m : kN (q * M')) : ℂ) = (qExpansion ((q * M' : ℕ) : ℝ) ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] γ)).coeff m :=
  Classical.choose_spec (exists_zc hqM' hk f hf γ m)

theorem coeff_slash_γt (t : (ZMod (q * M'))ˣ) (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M')))
    (hσ : σ (zetaK (q * M')) = zetaK (q * M') ^ ((t : ZMod (q * M'))).val) (m : ℕ) :
    (qExpansion ((q * M' : ℕ) : ℝ) ((⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ t))).coeff m =
      ((σ (zc hqM' hk f hf γ m) : kN (q * M')) : ℂ) := by
  obtain ⟨z, hz, hz'⟩ := key_recip hqM' hk f hf γ t σ hσ m
  have : z = zc hqM' hk f hf γ m := Subtype.ext (hz.trans (zc_spec hqM' hk f hf γ m).symm)
  rw [hz', phiOf_apply, this]

variable {γ} (hγ : γ ∈ Gamma0 M')
include hγ

theorem coeff_sl_γt (t : (ZMod (q * M'))ˣ) (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M')))
    (hσ : σ (zetaK (q * M')) = zetaK (q * M') ^ ((t : ZMod (q * M'))).val) (n : ℕ) :
    (qExpansion 1 (sl hqM' (γt γ t) (γt_mem_Gamma0 hγ t) f)).coeff n =
      (q : ℂ) ^ (k - 1) * ((σ (zc hqM' hk f hf γ (M' * n)) : kN (q * M')) : ℂ) := by
  rw [coeff_qExpansion_sl hqM' f (γt_mem_Gamma0 hγ t) (slashSL (γt γ t) (FF hqM' f)) (coe_slashSL _ _) n,
    coe_slashSL, ← ModularForm.SL_slash, coeff_slash_γt hqM' hk f hf γ t σ hσ]

theorem FF_slash_γt_eq_of_ured_eq {t t' : (ZMod (q * M'))ˣ} (h : ured t = ured t') :
    (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ t) = (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ t') := by
  rw [ModularForm.SL_slash, ModularForm.SL_slash, FF_slash_eq, FF_slash_eq,
    slash_conjElem_γt_eq_of_ured_eq hqM' f hγ h]

end Recip
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

section Forms

variable [NeZero M']

theorem pow_eq_pow_of_mod_eq {R : Type*} [Monoid R] {ζ : R} {n : ℕ} (hζ : ζ ^ n = 1) {x y : ℕ}
    (h : x % n = y % n) : ζ ^ x = ζ ^ y := by
  rw [← Nat.mod_add_div x n, ← Nat.mod_add_div y n, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow, one_pow, h]

def ι (u : (ZMod q)ˣ) : (ZMod (q * M'))ˣ :=
  Classical.choose (ZMod.unitsMap_surjective (dvd_mul_right q M') u)

theorem ured_ι (u : (ZMod q)ˣ) : ured (ι (M' := M') u) = u :=
  Classical.choose_spec (ZMod.unitsMap_surjective (dvd_mul_right q M') u)

def ιv (u : (ZMod q)ˣ) : ℕ := ((ι (M' := M') u : (ZMod (q * M'))ˣ) : ZMod (q * M')).val

theorem ιv_coprime (u : (ZMod q)ˣ) : (ιv (M' := M') u).Coprime (q * M') :=
  ZMod.val_coe_unit_coprime (ι (M' := M') u)

def σu (u : (ZMod q)ˣ) : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M')) :=
  Classical.choose (exists_aut_pow_eq (q * M') (ιv (M' := M') u) (ιv_coprime u))

theorem σu_spec (u : (ZMod q)ˣ) :
    σu (M' := M') u (zetaK (q * M')) = zetaK (q * M') ^ (((ι (M' := M') u : (ZMod (q * M'))ˣ) : ZMod (q * M'))).val :=
  Classical.choose_spec (exists_aut_pow_eq (q * M') (ιv (M' := M') u) (ιv_coprime u))

def zq (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

theorem isPrimitiveRoot_zq : IsPrimitiveRoot (zq q) q :=
  Complex.isPrimitiveRoot_exp q (Fact.out : q.Prime).ne_zero

theorem zetaC_pow_M' : zetaC (q * M') ^ M' = zq q := by
  rw [zetaC, zq, ← Complex.exp_nat_mul]
  congr 1
  have hM : (M' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M')
  push_cast
  field_simp [qneC q]

def zqK : kN (q * M') := zetaK (q * M') ^ M'

theorem coe_zqK : ((zqK (q := q) (M' := M') : kN (q * M')) : ℂ) = zq q := by
  rw [zqK]; push_cast; rw [coe_zetaK, zetaC_pow_M']

theorem zqK_pow_q : zqK (q := q) (M' := M') ^ q = 1 := by
  rw [zqK, ← pow_mul, mul_comm M' q]
  exact (isPrimitiveRoot_zetaK (q * M')).pow_eq_one

theorem zqK_pow_eq_of_natCast_eq {x y : ℕ} (h : (x : ZMod q) = (y : ZMod q)) :
    zqK (q := q) (M' := M') ^ x = zqK ^ y :=
  pow_eq_pow_of_mod_eq zqK_pow_q ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h)

theorem aut_zqK (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M'))) :
    σ (zqK (q := q) (M' := M')) =
      zqK ^ ((((isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ : (ZMod (q * M'))ˣ) : ZMod (q * M')).val) := by
  rw [zqK, map_pow, aut_zetaK (q * M') σ, ← pow_mul, ← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

def cc (j : ℕ) (u : (ZMod q)ˣ) : ℂ := ((zq q ^ (u : ZMod q).val) ^ j)⁻¹ - 1

def ccK (j : ℕ) (u : (ZMod q)ˣ) : kN (q * M') := ((zqK (q := q) (M' := M') ^ (u : ZMod q).val) ^ j)⁻¹ - 1

theorem coe_ccK (j : ℕ) (u : (ZMod q)ˣ) : ((ccK (M' := M') j u : kN (q * M')) : ℂ) = cc j u := by
  rw [ccK, cc]; push_cast; rw [coe_zqK]

theorem coe_finset_sum {k : ℤ} {ι' : Type*} (S : Finset ι') (g : ι' → ModularForm (Γ q M') k) :
    (⇑(∑ i ∈ S, g i) : ℍ → ℂ) = ∑ i ∈ S, (⇑(g i) : ℍ → ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

def hh (hqM' : ¬ q ∣ M') {k : ℤ} (f : ModularForm (Γ q M') k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (j : ℕ) :
    ModularForm (Γ q M') k :=
  (q : ℂ)⁻¹ • ∑ u : (ZMod q)ˣ, cc j u • sl hqM' (γt γ (ι u)) (γt_mem_Gamma0 hγ _) f

theorem coe_hh_apply (hqM' : ¬ q ∣ M') {k : ℤ} (f : ModularForm (Γ q M') k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M')
    (j : ℕ) (τ : ℍ) :
    hh hqM' f hγ j τ = (q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, cc j u * ((⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ (ι (M' := M') u))) τ := by
  simp only [hh, ModularForm.IsGLPos.coe_smul, Pi.smul_apply, coe_finset_sum, Finset.sum_apply, smul_eq_mul, coe_sl]

omit [NeZero M'] in

theorem exp_eq_zq_pow (s j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) = zq q ^ (s * j) := by
  rw [zq, ← Complex.exp_nat_mul]
  congr 1
  ring

omit [NeZero M'] in

theorem charSum (s : ℕ) (hs : s.Coprime q) (u : (ZMod q)ˣ) :
    ∑ j ∈ Finset.range q, zq q ^ (s * j) * cc j u = if u = ZMod.unitOfCoprime s hs then (q : ℂ) else 0 := by
  have hζ := isPrimitiveRoot_zq (q := q)
  set w : ℂ := zq q ^ s * (zq q ^ (u : ZMod q).val)⁻¹ with hw
  have hne : zq q ≠ 0 := hζ.ne_zero (Fact.out : q.Prime).ne_zero
  have hterm : ∀ j, zq q ^ (s * j) * cc j u = w ^ j - (zq q ^ s) ^ j := by
    intro j
    rw [cc, hw, mul_sub, mul_one, pow_mul, ← inv_pow, ← mul_pow]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, (hζ.pow_of_coprime s hs).geom_sum_eq_zero (one_lt_q q), sub_zero]
  have hwq : w ^ q = 1 := by
    rw [hw, mul_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm s q, Nat.mul_comm _ q, pow_mul, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, inv_one, mul_one]

  have hsmod : zq q ^ s = zq q ^ (s % q) := pow_eq_pow_of_mod_eq hζ.pow_eq_one (Nat.mod_mod _ _).symm
  split_ifs with hu
  ·
    have hval : zq q ^ (u : ZMod q).val = zq q ^ s := by
      rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← hsmod]
    have hw1 : w = 1 := by rw [hw, hval, mul_inv_cancel₀ (pow_ne_zero _ hne)]
    simp [hw1]
  ·
    have hw1 : w ≠ 1 := by
      intro h1
      apply hu
      rw [hw, mul_inv_eq_one₀ (pow_ne_zero _ hne), hsmod] at h1
      have h2 : s % q = (u : ZMod q).val := hζ.pow_inj (Nat.mod_lt s (qpos q)) (ZMod.val_lt _) h1
      have h3 : (s : ZMod q) = (u : ZMod q) := ZMod.val_injective q (by rw [ZMod.val_natCast, h2])
      exact Units.ext (by rw [ZMod.coe_unitOfCoprime]; exact h3.symm)
    rw [geom_sum_eq hw1, hwq, sub_self, zero_div]

theorem sum_exp_smul_hh (hqM' : ¬ q ∣ M') {k : ℤ} (f : ModularForm (Γ q M') k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M') (s : ℕ) (hs : s.Coprime q) :
    ∑ j ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) • (⇑(hh hqM' f hγ j) : ℍ → ℂ)
      = (⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ (ι (M' := M') (ZMod.unitOfCoprime s hs))) := by
  funext τ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coe_hh_apply, exp_eq_zq_pow]
  set g : (ZMod q)ˣ → ℂ := fun u => ((⇑f : ℍ → ℂ) ∣[k] conjElem q (γt γ (ι (M' := M') u))) τ with hg
  calc ∑ j ∈ Finset.range q, zq q ^ (s * j) * ((q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, cc j u * g u)
      = (q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, (∑ j ∈ Finset.range q, zq q ^ (s * j) * cc j u) * g u := by
        have lhs : ∑ j ∈ Finset.range q, zq q ^ (s * j) * ((q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, cc j u * g u)
            = ∑ j ∈ Finset.range q, ∑ u : (ZMod q)ˣ, (q : ℂ)⁻¹ * (zq q ^ (s * j) * cc j u * g u) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          ring
        have rhs : (q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, (∑ j ∈ Finset.range q, zq q ^ (s * j) * cc j u) * g u
            = ∑ u : (ZMod q)ˣ, ∑ j ∈ Finset.range q, (q : ℂ)⁻¹ * (zq q ^ (s * j) * cc j u * g u) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
        rw [lhs, rhs, Finset.sum_comm]
    _ = (q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ, (if u = ZMod.unitOfCoprime s hs then (q : ℂ) else 0) * g u := by
        simp_rw [charSum s hs]
    _ = g (ZMod.unitOfCoprime s hs) := by
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _), ← mul_assoc,
          inv_mul_cancel₀ (qneC q), one_mul]

theorem ured_mul (t t' : (ZMod (q * M'))ˣ) : ured (t * t') = ured t * ured t' := map_mul _ _ _

variable (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k) (f : ModularForm (Γ q M') k)
  (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

theorem coeff_hh (j n : ℕ) :
    (qExpansion 1 (hh hqM' f hγ j)).coeff n = (q : ℂ)⁻¹ * ∑ u : (ZMod q)ˣ,
      cc j u * ((q : ℂ) ^ (k - 1) * ((σu (M' := M') u (zc hqM' hk f hf γ (M' * n)) : kN (q * M')) : ℂ)) := by
  rw [hh, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods]
  have hsum : qExpansion 1 (⇑(∑ u : (ZMod q)ˣ, cc j u • sl hqM' (γt γ (ι u)) (γt_mem_Gamma0 hγ _) f) : ℍ → ℂ)
      = ∑ u : (ZMod q)ˣ, cc j u • qExpansion 1 (⇑(sl hqM' (γt γ (ι u)) (γt_mem_Gamma0 hγ _) f) : ℍ → ℂ) := by
    have := map_sum (ModularForm.qExpansionAddHom one_pos (one_mem_strictPeriods (q := q) (M' := M')) k)
      (fun u : (ZMod q)ˣ => cc j u • sl hqM' (γt γ (ι u)) (γt_mem_Gamma0 hγ _) f) Finset.univ
    refine this.trans (Finset.sum_congr rfl fun u _ => ?_)
    show qExpansion 1 (⇑(cc j u • sl hqM' (γt γ (ι u)) (γt_mem_Gamma0 hγ _) f) : ℍ → ℂ) = _
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods]
  rw [hsum]
  simp only [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_sl_γt hqM' hk f hf hγ (ι u) (σu u) (σu_spec u) n]

def dd (j n : ℕ) : kN (q * M') :=
  algebraMap ℚ (kN (q * M')) ((q : ℚ)⁻¹ * (q : ℚ) ^ (k - 1)) *
    ∑ u : (ZMod q)ˣ, ccK j u * σu u (zc hqM' hk f hf γ (M' * n))

theorem coe_dd (j n : ℕ) :
    ((dd hqM' hk f hf γ j n : kN (q * M')) : ℂ) = (qExpansion 1 (hh hqM' f hγ j)).coeff n := by
  rw [coeff_hh hqM' hk f hf γ hγ, dd, IntermediateField.coe_mul, coe_algebraMap_rat]
  push_cast [coe_ccK, Rat.cast_zpow]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

include hγ in

theorem aut_σu_zc (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M'))) (u : (ZMod q)ˣ) (m : ℕ) :
    σ (σu (M' := M') u (zc hqM' hk f hf γ m)) =
      σu (M' := M') (ured ((isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ) * u) (zc hqM' hk f hf γ m) := by
  set t : (ZMod (q * M'))ˣ := (isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ with ht
  have hσ : σ (zetaK (q * M')) = zetaK (q * M') ^ ((t : ZMod (q * M'))).val := aut_zetaK (q * M') σ

  have hσ' : (σ * σu (M' := M') u) (zetaK (q * M'))
      = zetaK (q * M') ^ (((t * ι (M' := M') u : (ZMod (q * M'))ˣ) : ZMod (q * M'))).val := by
    rw [AlgEquiv.mul_apply, σu_spec, map_pow, hσ, ← pow_mul, Units.val_mul, ZMod.val_mul, zetaK_pow_mod]
  apply Subtype.val_injective
  have h1 := coeff_slash_γt hqM' hk f hf γ (t * ι (M' := M') u) (σ * σu (M' := M') u) hσ' m
  have h2 := coeff_slash_γt hqM' hk f hf γ (ι (M' := M') (ured t * u)) (σu (M' := M') (ured t * u)) (σu_spec _) m
  have h3 : (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ (t * ι (M' := M') u))
      = (⇑(FF hqM' f) : ℍ → ℂ) ∣[k] (γt γ (ι (M' := M') (ured t * u))) :=
    FF_slash_γt_eq_of_ured_eq hqM' hk f hf hγ (by rw [ured_mul, ured_ι, ured_ι])
  rw [h3, h2] at h1
  simp only [AlgEquiv.mul_apply] at h1
  exact h1.symm

theorem aut_ccK (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M'))) (j : ℕ) (u : (ZMod q)ˣ) :
    σ (ccK (M' := M') j u) = ccK j (ured ((isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ) * u) := by
  set t : (ZMod (q * M'))ˣ := (isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ with ht
  simp only [ccK, map_sub, map_one, map_inv₀, map_pow, aut_zqK, ← ht]
  rw [← pow_mul (zqK (q := q) (M' := M')) _ (u : ZMod q).val]
  congr 3
  apply zqK_pow_eq_of_natCast_eq
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, coe_ured, ZMod.castHom_apply, ZMod.cast_eq_val]

include hγ in

theorem dd_fixed (j n : ℕ) (σ : (kN (q * M')) ≃ₐ[ℚ] (kN (q * M'))) :
    σ (dd hqM' hk f hf γ j n) = dd hqM' hk f hf γ j n := by
  set t : (ZMod (q * M'))ˣ := (isPrimitiveRoot_zetaK (q * M')).autToPow ℚ σ with ht
  rw [dd, map_mul, AlgEquiv.commutes, map_sum]
  congr 1
  simp_rw [map_mul, aut_ccK σ, aut_σu_zc hqM' hk f hf γ hγ σ, ← ht]
  exact Equiv.sum_comp (Equiv.mulLeft (ured t))
    (fun u' => ccK j u' * σu (M' := M') u' (zc hqM' hk f hf γ (M' * n)))

include hk hf in

theorem hh_rat (j n : ℕ) : ∃ r : ℚ, (qExpansion 1 (hh hqM' f hγ j)).coeff n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := exists_rat_of_fixed (q * M') (dd hqM' hk f hf γ j n) (dd_fixed hqM' hk f hf γ hγ j n)
  exact ⟨r, by rw [← coe_dd hqM' hk f hf γ hγ, hr]⟩

end Forms
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

theorem main [NeZero M'] (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k) (f : ModularForm (Γ q M') k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    ∃ h : ℕ → ModularForm (Γ q M') k,
      (∀ j n : ℕ, ∃ r : ℚ, (qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s q → γ' ∈ Gamma0 M' →
        !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)] →
        ((⇑f : ℍ → ℂ) ∣[k] conjElem q γ') =
          ∑ j ∈ Finset.range q,
            Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) • (⇑(h j) : ℍ → ℂ) := by
  refine ⟨hh hqM' f hγ, fun j n => hh_rat hqM' hk f hf γ hγ j n, fun s γ' hs hγ' hγγ' => ?_⟩
  rw [sum_exp_smul_hh hqM' f hγ s hs]
  exact slash_conjElem_eq_γt hqM' f hγ hs hγ' hγγ' (ured_ι _)

end W1pRR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

theorem solution (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ h : ℕ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
        Subgroup (GL (Fin 2) ℝ)) k,
      (∀ j n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s q → γ' ∈ CongruenceSubgroup.Gamma0 M' →
        !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)] →
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElem q γ') =
          ∑ j ∈ Finset.range q,
            Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) •
              (⇑(h j) : UpperHalfPlane → ℂ) := by
  haveI : NeZero M' := ⟨W1pRR.M'_ne_zero hqM'⟩
  exact W1pRR.main hqM' hk f hf hγ

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRR"

end S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0 (solution)
