-- Prove2me | solution 1 for ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0337b282-bac6-575b-82bb-e69d63c72236

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace A2ALInt

local notation "Δ" => ModularForm.discriminant

def IsRat (q : PowerSeries ℂ) : Prop := ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)

theorem isRat_iff_exists_map {q : PowerSeries ℂ} :
    IsRat q ↔ ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  constructor
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  · rintro ⟨p, rfl⟩ n
    exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

theorem IsRat.mul {q q' : PowerSeries ℂ} (h : IsRat q) (h' : IsRat q') : IsRat (q * q') := by
  rw [isRat_iff_exists_map] at h h' ⊢
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', rfl⟩ := h'
  exact ⟨p * p', by rw [map_mul]⟩

theorem IsRat.pow {q : PowerSeries ℂ} (h : IsRat q) (n : ℕ) : IsRat (q ^ n) := by
  rw [isRat_iff_exists_map] at h ⊢
  obtain ⟨p, rfl⟩ := h
  exact ⟨p ^ n, by rw [map_pow]⟩

theorem IsRat.of_mul_eq {q u p : PowerSeries ℂ} (hu : IsRat u) (hu0 : PowerSeries.constantCoeff u = 1)
    (hp : IsRat p) (h : q * u = p) : IsRat q := by
  rw [isRat_iff_exists_map] at hu hp ⊢
  obtain ⟨U, rfl⟩ := hu
  obtain ⟨P, rfl⟩ := hp
  have hU0 : PowerSeries.constantCoeff U = 1 := by
    have : algebraMap ℚ ℂ (PowerSeries.constantCoeff U) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hu0,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    exact (algebraMap ℚ ℂ).injective (by rw [this, map_one])
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU0]; exact isUnit_one
  obtain ⟨v, hv⟩ := hUunit
  refine ⟨P * ↑v⁻¹, ?_⟩
  have hne : (U.map (algebraMap ℚ ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0] at this
    simp at this
  apply mul_right_cancel₀ hne
  rw [h, map_mul, mul_assoc, ← map_mul, ← hv, Units.inv_mul, map_one, mul_one]

section Level

variable {M ℓ : ℕ} {k : ℤ}

abbrev ΓSL (M ℓ : ℕ) : Subgroup SL(2, ℤ) := Gamma1 M ⊓ Gamma0 (M * ℓ)

abbrev Γ' (M ℓ : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((ΓSL M ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem : ModularGroup.T ∈ ΓSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨by simp [Gamma1_mem, ModularGroup.T], ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods' : (1 : ℝ) ∈ (Γ' M ℓ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem]
  exact AddSubgroup.mem_zmultiples _

scoped instance [NeZero M] [NeZero ℓ] : (ΓSL M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)

def conjMat (ℓ : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (ℓ : ℤ) * δ 0 1; δ 1 0 / ℓ, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : (conjMat ℓ δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (ℓ : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_apply_10_eq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    ∃ c : ℤ, (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  refine ⟨c, ?_⟩
  show δ 1 0 / ℓ = M * c
  rw [hc]; push_cast
  rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
  exact Int.mul_ediv_cancel_left _ hℓ'

theorem conjSL_mem_Gamma1 {δ : SL(2, ℤ)} (hδ1 : δ ∈ Gamma1 M) (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma1 M := by
  obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ hℓ
  rw [Gamma1_mem] at hδ1 ⊢
  refine ⟨hδ1.1, hδ1.2.1, ?_⟩
  rw [hc]; push_cast; simp

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ δ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem conj_apply_10 (γ z : SL(2, ℤ)) :
    (γ * z * γ⁻¹) 1 0 = γ 1 0 * z 0 0 * γ 1 1 + γ 1 1 * z 1 0 * γ 1 1
      - γ 1 0 * z 0 1 * γ 1 0 - γ 1 1 * z 1 1 * γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    change ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

abbrev alGL (γ : SL(2, ℤ)) (ℓ : ℕ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ γ * ModularForm.heckeDiagMatrix ℓ

include hγ hγℓ in

theorem alConj_mem {δ : SL(2, ℤ)} (hδ1 : δ ∈ Gamma1 M) (hδ : δ ∈ Gamma0 (M * ℓ))
    (hℓ : ℓ ≠ 0) : γ * conjSL δ (dvd_of_mem_Gamma0_mul hδ) * γ⁻¹ ∈ ΓSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1 hγ (conjSL_mem_Gamma1 hδ1 hδ hℓ), ?_⟩
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, conj_apply_10]
  obtain ⟨r, hr⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨s, hs⟩ := hγℓ
  obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ hℓ
  rw [hc, conjSL_apply_00, conjSL_apply_01, conjSL_apply_11, hr, hs]
  exact ⟨r * δ 0 0 * s + s * c * ℓ * s - r * δ 0 1 * M * r - s * δ 1 1 * r, by push_cast; ring⟩

include hγ hγℓ in

theorem le_conj_al (hℓ : ℓ ≠ 0) : Γ' M ℓ ≤ ConjAct.toConjAct (alGL γ ℓ)⁻¹ • Γ' M ℓ := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδ1, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, alConj_mem γ hγ hγℓ hδ1 hδ0 hℓ, ?_⟩
  rw [map_mul, map_mul, map_inv, ← heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) hℓ]
  simp only [alGL, _root_.mul_inv_rev, mul_assoc]

variable [NeZero ℓ]

def alForm (f : ModularForm (Γ' M ℓ) k) : ModularForm (Γ' M ℓ) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (le_conj_al γ hγ hγℓ (NeZero.ne ℓ)) (ModularForm.translate f (alGL γ ℓ))

theorem alForm_apply (f : ModularForm (Γ' M ℓ) k) (τ : ℍ) :
    alForm γ hγ hγℓ f τ = (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] alGL γ ℓ) τ) = _
  rw [alGL, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]
  rfl

theorem coe_alForm (f : ModularForm (Γ' M ℓ) k) :
    ⇑(alForm γ hγ hγℓ f) = fun τ => (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (alForm_apply γ hγ hγℓ f)

theorem le_conj_SL : Γ' M ℓ ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • 𝒮ℒ := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨-, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) (NeZero.ne ℓ)).symm⟩

def levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) : ModularForm (Γ' M ℓ) kE :=
  ((ℓ : ℂ) ^ (kE - 1))⁻¹ • restrictForm le_conj_SL (ModularForm.translate E (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (τ : ℍ) :
    levelRaise (M := M) (ℓ := ℓ) E τ = E (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (kE - 1))⁻¹ • ((⇑E ∣[kE] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply kE (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coeff_qExpansion_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (n : ℕ) :
    (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E)).coeff n =
      if ℓ ∣ n then (qExpansion 1 E).coeff (n / ℓ) else 0 := by
  have hcoe : (⇑(levelRaise (M := M) (ℓ := ℓ) E) : ℍ → ℂ) = fun τ => E (ModularForm.heckeDiagMatrix ℓ • τ) :=
    funext (levelRaise_apply E)
  rw [hcoe]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul E one_mem_strictPeriods_SL (NeZero.ne ℓ) n

theorem isRat_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (hE : IsRat (qExpansion 1 E)) :
    IsRat (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E)) := by
  intro n
  rw [coeff_qExpansion_levelRaise]
  split_ifs
  · exact hE _
  · exact ⟨0, by simp⟩

theorem constantCoeff_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hE : PowerSeries.constantCoeff (qExpansion 1 (E : ℍ → ℂ)) = 1) :
    PowerSeries.constantCoeff (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_qExpansion_levelRaise, if_pos (dvd_zero ℓ),
    Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff_apply, hE]

omit [NeZero ℓ] in
include hγ in
theorem conj_T_pow_mem : γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹ ∈ ΓSL M ℓ := by
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨r, hr⟩ := hc
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have h00 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 0 0 = 1 - γ 0 0 * γ 1 0 * ℓ := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h11 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 1 1 = 1 + γ 0 0 * γ 1 0 * ℓ := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h10 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 1 0 = -(γ 1 0 * γ 1 0 * ℓ) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem, h00, h11, h10, hr]
    push_cast
    simp
  · rw [Gamma0_mem, h10, hr, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-(r * M * r), by push_cast; ring⟩

omit [NeZero ℓ] in
include hγ in

theorem natCast_mem_strictPeriods_conj :
    (ℓ : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ' M ℓ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    inv_inv, ConjAct.toConjAct_smul]
  refine ⟨_, conj_T_pow_mem γ hγ, ?_⟩
  have hT : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (ℓ : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (ℓ : ℝ) := by
    apply Units.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]
  rw [map_mul, map_mul, map_inv, hT]

omit [NeZero ℓ] in
include hγ in

theorem periodic_slash (f : ModularForm (Γ' M ℓ) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] γ) ∘ ofComplex) ℓ := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ))
    (natCast_mem_strictPeriods_conj (M := M) γ hγ)
  rwa [SlashInvariantForm.coe_translate] at this

theorem isBoundedAtImInfty_slash [NeZero M] (f : ModularForm (Γ' M ℓ) k) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] α) := by
  rw [ModularForm.SL_slash, ← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply f.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨α, rfl⟩

end Level

section Weight

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {k : ℤ}

theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

theorem levelOne_smul {k' : ℤ} (E : ModularForm 𝒮ℒ k') (α : SL(2, ℤ)) (τ : ℍ) :
    E (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ k' * E τ := by
  have := SlashInvariantForm.slash_action_eqn'' E (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [← ModularGroup.sl_moeb] at this
  exact this

omit [NeZero M] [NeZero ℓ] in
theorem periodic_disc_natCast : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) (ℓ : ℂ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rw [CuspForm.coe_discriminant] at this
  simpa using this.nat_mul ℓ

omit [NeZero M] [NeZero ℓ] in
theorem periodic_levelOne_natCast {k' : ℤ} (E : ModularForm 𝒮ℒ k') : Periodic ((⇑E : ℍ → ℂ) ∘ ofComplex) (ℓ : ℂ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex E one_mem_strictPeriods_SL
  simpa using this.nat_mul ℓ

theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem isRat_slash_mul (f : ModularForm (Γ' M ℓ) k) (m : ℕ) {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hkE : k + kE = 12 * m) (hf : IsRat (qExpansion 1 f)) (hE : IsRat (qExpansion 1 E))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∀ n, ∃ r : ℚ, (qExpansion ℓ (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E)).coeff n = (r : ℂ) := by

  set H : ℍ → ℂ := (⇑f : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := f.holo'.mul E.holo'
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul E, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + kE) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hkE]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero kE hd]

  have hinv : ∀ g ∈ ΓSL M ℓ, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = f τ * E τ := by
      have := congrFun hGΔ τ; (simp only [Pi.mul_apply, Pi.pow_apply] at this; exact this)
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (isBoundedAtImInfty_slash f α).mul (ModularFormClass.bdd_at_infty E)

  have hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ) := by
    rw [hGΔ, hH]
    have : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E) =
        qExpansion 1 ⇑f * qExpansion 1 ⇑(restrictForm (Subgroup.map_le_range _ _) E : ModularForm (Γ' M ℓ) kE) := by
      rw [← ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods' f
        (restrictForm (Subgroup.map_le_range _ _) E : ModularForm (Γ' M ℓ) kE)]
      rfl
    rw [this]
    exact hf.mul hE

  have key := ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd M ℓ m G hmdG hinv hbd
    hrat γ hγ hγℓ
  rw [hcw γ] at key
  exact key

theorem isRat_E4 : IsRat (qExpansion 1 (E₄ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

theorem isRat_E6 : IsRat (qExpansion 1 (E₆ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

theorem constantCoeff_E4 : PowerSeries.constantCoeff (qExpansion 1 (E₄ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₄,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

theorem constantCoeff_E6 : PowerSeries.constantCoeff (qExpansion 1 (E₆ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₆,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

def Eaux (a b : ℕ) : ModularForm 𝒮ℒ (a * 4 + b * 6) := (E₄.pow a).mul (E₆.pow b)

theorem qExpansion_Eaux (a b : ℕ) :
    qExpansion 1 (⇑(Eaux a b)) = qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b := by
  rw [Eaux, coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isRat_Eaux (a b : ℕ) : IsRat (qExpansion 1 (⇑(Eaux a b))) := by
  rw [qExpansion_Eaux]; exact (isRat_E4.pow a).mul (isRat_E6.pow b)

theorem constantCoeff_Eaux (a b : ℕ) : PowerSeries.constantCoeff (qExpansion 1 (⇑(Eaux a b))) = 1 := by
  rw [qExpansion_Eaux, map_mul, map_pow, map_pow, constantCoeff_E4, constantCoeff_E6, one_pow, one_pow,
    one_mul]

theorem exists_weights (hk : Even k) : ∃ (m a b : ℕ), k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ) := by
  obtain ⟨j, rfl⟩ := hk
  have hjabs : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hjabs' : -j ≤ (j.natAbs : ℤ) := by
    have := Int.le_natAbs (a := -j); rwa [Int.natAbs_neg] at this
  rcases Int.emod_two_eq_zero_or_one j with hpar | hpar
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 3 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 0, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q + 1 := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 1 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 1, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega

end Weight

section Width

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {k : ℤ}

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

theorem qParam_heckeDiag_smul (τ : ℍ) :
    Periodic.qParam (ℓ : ℝ) ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = Periodic.qParam 1 τ := by
  simp only [Periodic.qParam]
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ)]
  congr 1
  have : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  push_cast
  field_simp

theorem qExpansion_coeff_comp_heckeDiag {Φ Ψ : ℍ → ℂ} (hper : Periodic (Φ ∘ ofComplex) (ℓ : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Φ) (hbd : IsBoundedAtImInfty Φ)
    (hΨ : ∀ τ, Ψ τ = Φ (ModularForm.heckeDiagMatrix ℓ • τ)) (hΨan : AnalyticAt ℂ (cuspFunction 1 Ψ) 0)
    (n : ℕ) : (qExpansion 1 Ψ).coeff n = (qExpansion ℓ Φ).coeff n := by
  have hℓpos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (NeZero.pos ℓ)
  have hper' : Periodic (Φ ∘ ofComplex) ((ℓ : ℝ) : ℂ) := by simpa using hper
  have hsum : ∀ τ : ℍ, HasSum (fun m => (qExpansion ℓ Φ).coeff m • Periodic.qParam 1 τ ^ m) (Ψ τ) := by
    intro τ
    have := hasSum_qExpansion hℓpos hper' hhol hbd (ModularForm.heckeDiagMatrix ℓ • τ)
    rw [qParam_heckeDiag_smul (ℓ := ℓ), ← hΨ] at this
    exact this
  exact (qExpansion_coeff_unique' one_pos hΨan hsum n).symm

theorem isRat_alForm (hk : Even k) (f : ModularForm (Γ' M ℓ) k) (hf : IsRat (qExpansion 1 f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    IsRat (qExpansion 1 (alForm γ hγ hγℓ f)) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  set E := Eaux a b with hEdef
  have key := isRat_slash_mul f m E (by exact_mod_cast hw) hf (isRat_Eaux a b) hγ hγℓ

  set Ψ := (alForm γ hγ hγℓ f).mul (levelRaise (M := M) (ℓ := ℓ) E) with hΨ
  have hΨapply : ∀ τ, (Ψ : ℍ → ℂ) τ = (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) (ModularForm.heckeDiagMatrix ℓ • τ) := by
    intro τ
    simp only [hΨ, ModularForm.coe_mul, Pi.mul_apply, alForm_apply, levelRaise_apply]
  have hper : Periodic ((((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) ∘ ofComplex) (ℓ : ℂ) :=
    periodic_mul (periodic_slash γ hγ f) (periodic_levelOne_natCast E)
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) :=
    (f.holo'.slash k _).mul E.holo'
  have hbd : IsBoundedAtImInfty (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) :=
    (isBoundedAtImInfty_slash f γ).mul (ModularFormClass.bdd_at_infty E)
  have hΨan : AnalyticAt ℂ (cuspFunction 1 (Ψ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Ψ one_pos one_mem_strictPeriods'
  have hΨrat : IsRat (qExpansion 1 (Ψ : ℍ → ℂ)) := by
    intro n
    rw [qExpansion_coeff_comp_heckeDiag hper hhol hbd hΨapply hΨan n]
    exact key n
  have hprod : qExpansion 1 (Ψ : ℍ → ℂ) =
      qExpansion 1 (alForm γ hγ hγℓ f) * qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E) := by
    rw [hΨ, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods']
  exact IsRat.of_mul_eq (isRat_levelRaise E (isRat_Eaux a b))
    (constantCoeff_levelRaise E (constantCoeff_Eaux a b)) hΨrat hprod.symm

end Width

theorem cardK (M ℓ : ℕ) [NeZero M] [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ' M ℓ) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      IsIntegralQExp ((D : ℂ) • fun τ : ℍ => ((⇑f : ℍ → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ := by
  haveI : NeZero (M * ℓ) := NeZero.mul

  have hf : IsRat (qExpansion 1 f) := fun n => ⟨((PowerSeries.coeff n p : ℤ) : ℚ), by
    rw [← hp.coeff n]; push_cast; rfl⟩
  have hrat := isRat_alForm hk f hf γ hγ hγℓ

  have hle : ((Gamma1 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ' M ℓ :=
    Subgroup.map_mono (le_inf (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)) (Gamma1_in_Gamma0 _))
  obtain ⟨D, p₁, hD, hp₁⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M * ℓ)
    (restrictForm hle (alForm γ hγ hγℓ f)) hrat
  refine ⟨D, p₁, hD, ?_⟩
  rw [← coe_alForm γ hγ hγℓ f]
  exact hp₁

end A2ALInt
p2m_reactivate "P2MW.S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.A2ALInt"

open scoped MatrixGroups ModularForm in
theorem solution (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) :
      Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp
        ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ :=
  A2ALInt.cardK M ℓ hk f hp γ hγ hγℓ

end
end S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
end P2MW
export P2MW.S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (solution)
