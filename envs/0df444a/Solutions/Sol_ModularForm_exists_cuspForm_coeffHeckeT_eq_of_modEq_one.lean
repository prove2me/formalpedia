-- Prove2me | solution 1 for ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c9749273-562b-5a4e-889d-9a8e42e76352

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open ModularForm CongruenceSubgroup

noncomputable section

namespace EisensteinHeckeCongruence

variable (N ℓ : ℕ)

def betaZ (i : Fin (ℓ + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < ℓ then !![1, (N : ℤ) * (i : ℕ); 0, ℓ] else !![(ℓ : ℤ), 0; 0, 1]

def betaGL (i : Fin (ℓ + 1)) : GL (Fin 2) ℝ :=
  if (i : ℕ) < ℓ then heckeMatrix ℓ (N * (i : ℕ)) else heckeDiagMatrix ℓ

variable {N ℓ}

theorem betaZ_of_lt {i : Fin (ℓ + 1)} (hi : (i : ℕ) < ℓ) :
    betaZ N ℓ i = !![1, (N : ℤ) * (i : ℕ); 0, ℓ] := by rw [betaZ, if_pos hi]

theorem betaZ_of_not_lt {i : Fin (ℓ + 1)} (hi : ¬ (i : ℕ) < ℓ) :
    betaZ N ℓ i = !![(ℓ : ℤ), 0; 0, 1] := by rw [betaZ, if_neg hi]

theorem betaGL_of_lt {i : Fin (ℓ + 1)} (hi : (i : ℕ) < ℓ) :
    betaGL N ℓ i = heckeMatrix ℓ (N * (i : ℕ)) := by rw [betaGL, if_pos hi]

theorem betaGL_of_not_lt {i : Fin (ℓ + 1)} (hi : ¬ (i : ℕ) < ℓ) :
    betaGL N ℓ i = heckeDiagMatrix ℓ := by rw [betaGL, if_neg hi]

theorem eq_last_of_not_lt {i : Fin (ℓ + 1)} (hi : ¬ (i : ℕ) < ℓ) : i = Fin.last ℓ := by
  ext; rw [Fin.val_last]; omega

theorem val_betaGL (hℓ : ℓ ≠ 0) (i : Fin (ℓ + 1)) :
    ((betaGL N ℓ i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (betaZ N ℓ i).map (Int.castRingHom ℝ) := by
  by_cases hi : (i : ℕ) < ℓ
  · rw [betaGL_of_lt hi, betaZ_of_lt hi, val_heckeMatrix hℓ]
    ext a b; fin_cases a <;> fin_cases b <;> simp
  · rw [betaGL_of_not_lt hi, betaZ_of_not_lt hi, val_heckeDiagMatrix hℓ]
    ext a b; fin_cases a <;> fin_cases b <;> simp

theorem betaGL_one_zero (hℓ : ℓ ≠ 0) (i : Fin (ℓ + 1)) : (betaGL N ℓ i : GL (Fin 2) ℝ) 1 0 = 0 := by
  by_cases hi : (i : ℕ) < ℓ
  · rw [betaGL_of_lt hi]; simp [val_heckeMatrix hℓ]
  · rw [betaGL_of_not_lt hi]; simp [val_heckeDiagMatrix hℓ]

theorem det_betaZ (i : Fin (ℓ + 1)) : (betaZ N ℓ i).det = ℓ := by
  by_cases hi : (i : ℕ) < ℓ
  · rw [betaZ_of_lt hi, Matrix.det_fin_two_of]; ring
  · rw [betaZ_of_not_lt hi, Matrix.det_fin_two_of]; ring

theorem map_betaZ_zmod (hℓ1 : (ℓ : ZMod N) = 1) (i : Fin (ℓ + 1)) :
    (betaZ N ℓ i).map (Int.castRingHom (ZMod N)) = 1 := by
  by_cases hi : (i : ℕ) < ℓ
  · rw [betaZ_of_lt hi]
    ext a b; fin_cases a <;> fin_cases b <;> simp [hℓ1]
  · rw [betaZ_of_not_lt hi]
    ext a b; fin_cases a <;> fin_cases b <;> simp [hℓ1]

theorem val_coeGL (γ : SL(2, ℤ)) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) :=
  rfl

theorem map_coe_zmod_mul_inv (γ : SL(2, ℤ)) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N))) *
      ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 := by
  rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_coe_zmod_inv_mul (γ : SL(2, ℤ)) :
    (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N))) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 := by
  rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem coe_mul_coe_inv (γ : SL(2, ℤ)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem mem_Gamma_of_map_eq_one {δ : SL(2, ℤ)}
    (h : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1) : δ ∈ Gamma N := by
  rw [Gamma_mem]
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.map_apply, eq_intCast, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    zero_ne_one, one_ne_zero, not_false_eq_true] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem mem_Gamma_of_conj_eq (hℓ1 : (ℓ : ZMod N) = 1) (γ δ : SL(2, ℤ)) (i i' : Fin (ℓ + 1))
    (h : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * betaZ N ℓ i * γ = δ * betaZ N ℓ i') :
    δ ∈ Gamma N := by
  apply mem_Gamma_of_map_eq_one
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom (ZMod N))) h
  simp only [Matrix.map_mul, map_betaZ_zmod hℓ1, mul_one, map_coe_zmod_inv_mul] at this
  exact this.symm

theorem exists_conj_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (γ : SL(2, ℤ)) (i : Fin (ℓ + 1)) :
    ∃ (i' : Fin (ℓ + 1)) (δ : SL(2, ℤ)),
      ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * betaZ N ℓ i * γ = δ * betaZ N ℓ i' := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * betaZ N ℓ i * γ
    with hM
  have hdet : M.det = ℓ := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
      Matrix.SpecialLinearGroup.det_coe, det_betaZ, one_mul, mul_one]
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  obtain ⟨B, a, b, d, ha, hb, hbd, had, hMB⟩ :=
    Matrix.exists_specialLinearGroup_mul_upperTriangular M (hdet ▸ hℓ0)
  rw [hdet] at had
  have hd : 0 < d := pos_of_mul_pos_right (had.symm ▸ (by exact_mod_cast hℓ.pos)) ha.le
  rw [abs_of_pos hd] at hbd

  have hadvd : a.natAbs ∣ ℓ := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, abs_of_pos ha]; exact ⟨d, had.symm⟩
  rcases (Nat.dvd_prime hℓ).mp hadvd with ha1 | haℓ
  ·
    have ha1' : a = 1 := by rw [← abs_of_pos ha, ← Int.natCast_natAbs, ha1, Nat.cast_one]
    subst ha1'
    rw [one_mul] at had
    subst had

    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hN0 : (N : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    set j' : ℕ := ((b : ZMod ℓ) * (N : ZMod ℓ)⁻¹).val with hj'
    have hj'lt : j' < ℓ := ZMod.val_lt _
    have hcong : ((ℓ : ℕ) : ℤ) ∣ (N : ℤ) * j' - b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hj', ZMod.natCast_zmod_val, mul_comm (b : ZMod ℓ), ← mul_assoc, mul_inv_cancel₀ hN0,
        one_mul, sub_self]
    obtain ⟨m, hm⟩ := hcong
    refine ⟨⟨j', by omega⟩, B * ModularGroup.T ^ (-m), ?_⟩
    rw [hMB, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
      betaZ_of_lt (by exact hj'lt), Matrix.mul_assoc]
    congr 1
    ext x y; fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -hm
  ·
    have haℓ' : a = ℓ := by rw [← abs_of_pos ha, ← Int.natCast_natAbs, haℓ]
    rw [haℓ'] at had
    have hd1 : d = 1 := by
      have := mul_left_cancel₀ hℓ0 (had.trans (mul_one _).symm)
      exact this
    subst hd1
    have hb0 : b = 0 := by omega
    refine ⟨Fin.last ℓ, B, ?_⟩
    rw [hMB, betaZ_of_not_lt (by simp), haℓ', hb0]

theorem eq_of_coe_mul_betaGL_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {i i' : Fin (ℓ + 1)} (ε : SL(2, ℤ))
    (h : (ε : GL (Fin 2) ℝ) * betaGL N ℓ i = betaGL N ℓ i') : i = i' := by
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hℓp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hE := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ)) h
  simp only [Units.val_mul, val_coeGL, val_betaGL hℓ0, ← Matrix.map_mul] at hE
  have hZ : (ε : Matrix (Fin 2) (Fin 2) ℤ) * betaZ N ℓ i = betaZ N ℓ i' :=
    Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℝ)) hE
  clear hE h
  by_cases hi : (i : ℕ) < ℓ <;> by_cases hi' : (i' : ℕ) < ℓ
  · rw [betaZ_of_lt hi, betaZ_of_lt hi'] at hZ
    have h00 := congrFun (congrFun hZ 0) 0
    have h01 := congrFun (congrFun hZ 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    rw [h00, one_mul] at h01

    have hdvd : (ℓ : ℤ) ∣ (N : ℤ) * ((i' : ℕ) - (i : ℕ)) := ⟨ε 0 1, by linear_combination -h01⟩
    rcases hℓp.dvd_or_dvd hdvd with h1 | h1
    · exact absurd (Int.natCast_dvd_natCast.mp h1) hℓN
    · have := Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; constructor <;> omega)
      ext; omega
  · rw [betaZ_of_lt hi, betaZ_of_not_lt hi'] at hZ
    have h10 := congrFun (congrFun hZ 1) 0
    have h11 := congrFun (congrFun hZ 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10 h11
    rw [h10, zero_mul, zero_add] at h11
    have : (ℓ : ℤ) = 1 := Int.eq_one_of_mul_eq_one_left (by exact_mod_cast hℓ.pos.le) h11
    exact absurd (by exact_mod_cast this) hℓ.one_lt.ne'
  · rw [betaZ_of_not_lt hi, betaZ_of_lt hi'] at hZ
    have h00 := congrFun (congrFun hZ 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    have : (ℓ : ℤ) = 1 := Int.eq_one_of_mul_eq_one_left (by exact_mod_cast hℓ.pos.le) h00
    exact absurd (by exact_mod_cast this) hℓ.one_lt.ne'
  · rw [eq_last_of_not_lt hi, eq_last_of_not_lt hi']

section Sigma

variable (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (γ : SL(2, ℤ))
include hℓ hℓN

def sigma (i : Fin (ℓ + 1)) : Fin (ℓ + 1) := (exists_conj_eq hℓ hℓN γ i).choose

def delta (i : Fin (ℓ + 1)) : SL(2, ℤ) := (exists_conj_eq hℓ hℓN γ i).choose_spec.choose

theorem conj_eq (i : Fin (ℓ + 1)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * betaZ N ℓ i * γ
      = delta hℓ hℓN γ i * betaZ N ℓ (sigma hℓ hℓN γ i) :=
  (exists_conj_eq hℓ hℓN γ i).choose_spec.choose_spec

theorem delta_mem (hℓ1 : (ℓ : ZMod N) = 1) (i : Fin (ℓ + 1)) : delta hℓ hℓN γ i ∈ Gamma N :=
  mem_Gamma_of_conj_eq hℓ1 γ _ i _ (conj_eq hℓ hℓN γ i)

theorem conj_eq_GL' (i : Fin (ℓ + 1)) :
    ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * betaGL N ℓ i * γ
      = (delta hℓ hℓN γ i : GL (Fin 2) ℝ) * betaGL N ℓ (sigma hℓ hℓN γ i) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ))
    (conj_eq hℓ hℓN γ i)
  simp only [Matrix.map_mul] at h
  ext1
  simp only [Units.val_mul, val_coeGL, val_betaGL hℓ.ne_zero]
  exact h

theorem conj_eq_GL (i : Fin (ℓ + 1)) :
    (γ : GL (Fin 2) ℝ)⁻¹ * betaGL N ℓ i * γ
      = (delta hℓ hℓN γ i : GL (Fin 2) ℝ) * betaGL N ℓ (sigma hℓ hℓN γ i) := by
  have e : ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ)⁻¹ := by simp
  rw [← e]
  exact conj_eq_GL' hℓ hℓN γ i

theorem betaGL_mul (i : Fin (ℓ + 1)) :
    betaGL N ℓ i * (γ : GL (Fin 2) ℝ)
      = (γ : GL (Fin 2) ℝ) * (delta hℓ hℓN γ i : GL (Fin 2) ℝ) * betaGL N ℓ (sigma hℓ hℓN γ i) := by
  rw [mul_assoc, ← conj_eq_GL hℓ hℓN γ i]; group

theorem sigma_injective : Function.Injective (sigma hℓ hℓN γ) := by
  intro i₁ i₂ h
  have h₁ := conj_eq_GL hℓ hℓN γ i₁
  have h₂ := conj_eq_GL hℓ hℓN γ i₂
  rw [h] at h₁
  set g : GL (Fin 2) ℝ := (γ : GL (Fin 2) ℝ)
  set d₁ : GL (Fin 2) ℝ := (delta hℓ hℓN γ i₁ : GL (Fin 2) ℝ)
  set d₂ : GL (Fin 2) ℝ := (delta hℓ hℓN γ i₂ : GL (Fin 2) ℝ)
  have key : ((γ * delta hℓ hℓN γ i₂ * (delta hℓ hℓN γ i₁)⁻¹ * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      * betaGL N ℓ i₁ = betaGL N ℓ i₂ := by
    have e : ((γ * delta hℓ hℓN γ i₂ * (delta hℓ hℓN γ i₁)⁻¹ * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = g * d₂ * d₁⁻¹ * g⁻¹ := by simp [g, d₁, d₂]
    rw [e]
    calc g * d₂ * d₁⁻¹ * g⁻¹ * betaGL N ℓ i₁
        = g * d₂ * (d₁⁻¹ * (g⁻¹ * betaGL N ℓ i₁ * g)) * g⁻¹ := by group
      _ = g * (d₂ * betaGL N ℓ (sigma hℓ hℓN γ i₂)) * g⁻¹ := by rw [h₁]; group
      _ = betaGL N ℓ i₂ := by rw [← h₂]; group
  exact eq_of_coe_mul_betaGL_eq hℓ hℓN _ key

theorem sigma_bijective : Function.Bijective (sigma hℓ hℓN γ) :=
  (Finite.injective_iff_bijective).mp (sigma_injective hℓ hℓN γ)

end Sigma

def heckeT' (k : ℤ) (N ℓ : ℕ) (h : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ i : Fin (ℓ + 1), h ∣[k] betaGL N ℓ i

theorem heckeMatrix_eq_T_pow_mul (hℓ : ℓ ≠ 0) (n : ℕ) :
    heckeMatrix ℓ n = ((ModularGroup.T ^ ((n / ℓ : ℕ) : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
      * heckeMatrix ℓ (n % ℓ) := by
  ext1
  rw [Units.val_mul, val_coeGL, ModularGroup.coe_T_zpow, val_heckeMatrix hℓ, val_heckeMatrix hℓ]
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← Int.natCast_div, Int.cast_natCast]
  exact_mod_cast (Nat.mod_add_div' n ℓ).symm

theorem heckeT_eq_heckeT' (k : ℤ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {f : UpperHalfPlane → ℂ}
    (hT : ∀ m : ℤ, f ∣[k] ((ModularGroup.T ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ) = f) :
    heckeT k ℓ f = heckeT' k N ℓ f := by
  rw [heckeT', Fin.sum_univ_castSucc, betaGL_of_not_lt (by simp), heckeT_def]
  congr 1
  have key : ∀ n : ℕ, f ∣[k] heckeMatrix ℓ n = f ∣[k] heckeMatrix ℓ (n % ℓ) := fun n => by
    rw [heckeMatrix_eq_T_pow_mul hℓ.ne_zero n, SlashAction.slash_mul, hT]
  have hrhs : ∀ i : Fin ℓ, f ∣[k] betaGL N ℓ (Fin.castSucc i)
      = f ∣[k] heckeMatrix ℓ ((N * (i : ℕ)) % ℓ) := fun i => by
    rw [betaGL_of_lt (by simp), key]; rfl
  simp_rw [hrhs]

  let e : Fin ℓ → Fin ℓ := fun i => ⟨N * (i : ℕ) % ℓ, Nat.mod_lt _ hℓ.pos⟩
  have he : Function.Bijective e := by
    rw [← Finite.injective_iff_bijective]
    intro i₁ i₂ h
    have h' : N * (i₁ : ℕ) % ℓ = N * (i₂ : ℕ) % ℓ := congrArg Fin.val h
    have hcop : ℓ.gcd N = 1 := Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hcop h') i₁.2 i₂.2)
  rw [Finset.sum_range (fun j => f ∣[k] heckeMatrix ℓ j)]
  exact (he.sum_comp (fun j : Fin ℓ => f ∣[k] heckeMatrix ℓ (j : ℕ))).symm

theorem heckeT'_slash (k : ℤ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : (ℓ : ZMod N) = 1)
    {f : UpperHalfPlane → ℂ} (hf : ∀ δ ∈ Gamma N, f ∣[k] (δ : GL (Fin 2) ℝ) = f) (γ : SL(2, ℤ)) :
    (heckeT' k N ℓ f) ∣[k] (γ : GL (Fin 2) ℝ) = heckeT' k N ℓ (f ∣[k] (γ : GL (Fin 2) ℝ)) := by
  simp only [heckeT', SlashAction.sum_slash]
  have hterm : ∀ i : Fin (ℓ + 1), (f ∣[k] betaGL N ℓ i) ∣[k] (γ : GL (Fin 2) ℝ)
      = (f ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] betaGL N ℓ (sigma hℓ hℓN γ i) := fun i => by
    rw [← SlashAction.slash_mul, betaGL_mul hℓ hℓN γ i, SlashAction.slash_mul,
      SlashAction.slash_mul]
    congr 1

    have hmem : γ * delta hℓ hℓN γ i * γ⁻¹ ∈ Gamma N :=
      (Gamma_normal N).conj_mem _ (delta_mem hℓ hℓN γ hℓ1 i) γ
    rw [← SlashAction.slash_mul,
      show (γ : GL (Fin 2) ℝ) * (delta hℓ hℓN γ i : GL (Fin 2) ℝ)
        = ((γ * delta hℓ hℓN γ i * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * γ by simp,
      SlashAction.slash_mul, hf _ hmem]
  simp_rw [hterm]
  exact (sigma_bijective hℓ hℓN γ).sum_comp (fun i => (f ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] betaGL N ℓ i)

section Analytic

open UpperHalfPlane Filter Topology
open scoped Manifold

theorem tendsto_atImInfty_of_periodic {h : UpperHalfPlane → ℂ} {H : ℝ} (hH : 0 < H)
    (hper : Function.Periodic (h ∘ UpperHalfPlane.ofComplex) H)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hbdd : IsBoundedAtImInfty h) :
    Tendsto h atImInfty (𝓝 (cuspFunction H h 0)) := by
  have hc := (analyticAt_cuspFunction_zero hH hper hhol hbdd).continuousAt
  exact (hc.tendsto.comp (qParam_tendsto_atImInfty hH)).congr fun τ => eq_cuspFunction τ hH.ne' hper

theorem tendsto_heckeT'_sub (k : ℤ) (hℓ : ℓ ≠ 0) {h : UpperHalfPlane → ℂ} {L : ℂ}
    (hL : Tendsto h atImInfty (𝓝 L)) :
    Tendsto (fun τ => heckeT' k N ℓ h τ - (1 + (ℓ : ℂ) ^ (k - 1)) * h τ) atImInfty (𝓝 0) := by
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ

  let c : Fin (ℓ + 1) → ℂ := fun i => if (i : ℕ) < ℓ then (ℓ : ℂ)⁻¹ * L else (ℓ : ℂ) ^ (k - 1) * L
  have hterm : ∀ i : Fin (ℓ + 1),
      Tendsto (fun τ => (h ∣[k] betaGL N ℓ i) τ) atImInfty (𝓝 (c i)) := by
    intro i
    have hlim : Tendsto (fun τ => h (betaGL N ℓ i • τ)) atImInfty (𝓝 L) :=
      hL.comp (tendsto_smul_atImInfty (betaGL_one_zero hℓ i))
    by_cases hi : (i : ℕ) < ℓ
    · simp only [c, if_pos hi, betaGL_of_lt hi] at hlim ⊢
      simp_rw [slash_heckeMatrix_apply k hℓ]
      exact hlim.const_mul _
    · simp only [c, if_neg hi, betaGL_of_not_lt hi] at hlim ⊢
      simp_rw [slash_heckeDiagMatrix_apply k hℓ]
      exact hlim.const_mul _
  have hsum : Tendsto (fun τ => heckeT' k N ℓ h τ) atImInfty (𝓝 (∑ i : Fin (ℓ + 1), c i)) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (ℓ + 1))) (fun i _ => hterm i)
    refine this.congr fun τ => ?_
    simp only [heckeT', Finset.sum_apply]
  have hc : ∑ i : Fin (ℓ + 1), c i = (1 + (ℓ : ℂ) ^ (k - 1)) * L := by
    rw [Fin.sum_univ_castSucc]
    simp only [c, Fin.val_castSucc, Fin.is_lt, if_true, Fin.val_last, lt_self_iff_false, if_false,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hℓ', one_mul]
    ring
  rw [hc] at hsum
  have := hsum.sub (hL.const_mul (1 + (ℓ : ℂ) ^ (k - 1)))
  rwa [sub_self] at this

end Analytic

section Assembly

open UpperHalfPlane Filter Topology
open scoped Manifold

theorem not_dvd_of_modEq_one {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N]) : ¬ ℓ ∣ N := by
  intro hdvd
  have h1 : N ∣ ℓ - 1 := (Nat.modEq_iff_dvd' hℓ.one_lt.le).mp hℓ1.symm
  have h2 : ℓ ∣ ℓ - 1 := dvd_trans hdvd h1
  have h3 := Nat.le_of_dvd (by have := hℓ.two_le; omega) h2
  have := hℓ.two_le
  omega

variable {N : ℕ} [NeZero N] {k : ℤ}

local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def slashSIF (f : ModularForm Γ₀(N) k) (γ : SL(2, ℤ)) : SlashInvariantForm (Gamma N) k where
  toFun := (⇑f) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    rintro _ ⟨δ, hδ, rfl⟩
    have hmem : γ * δ * γ⁻¹ ∈ Gamma0 N := by
      have := (Gamma_normal N).conj_mem _ hδ γ
      rw [Gamma_mem] at this
      exact Gamma0_mem.mpr this.2.2.1
    have hinv : (⇑f) ∣[k] ((γ * δ * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f :=
      SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
    show (⇑f ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (δ : GL (Fin 2) ℝ) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul,
      show (γ : GL (Fin 2) ℝ) * (δ : GL (Fin 2) ℝ) = ((γ * δ * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * γ by simp,
      SlashAction.slash_mul, hinv]

theorem isZeroAtImInfty_slash (f : ModularForm Γ₀(N) k) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ1 : ℓ ≡ 1 [MOD N]) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty ((heckeT k ℓ ⇑f - (1 + (ℓ : ℂ) ^ (k - 1)) • ⇑f) ∣[k] (γ : GL (Fin 2) ℝ)) := by
  have hℓN : ¬ ℓ ∣ N := not_dvd_of_modEq_one hℓ hℓ1
  have hℓ1' : (ℓ : ZMod N) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff ℓ 1 N).mpr hℓ1; rwa [Nat.cast_one] at this

  have hf0 : ∀ δ ∈ Gamma0 N, (⇑f) ∣[k] (δ : GL (Fin 2) ℝ) = ⇑f := fun δ hδ =>
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hδ)
  have hT : ∀ m : ℤ, (⇑f) ∣[k] ((ModularGroup.T ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f := fun m =>
    hf0 _ (by simp [ModularGroup.coe_T_zpow])
  have hfΓ : ∀ δ ∈ Gamma N, (⇑f) ∣[k] (δ : GL (Fin 2) ℝ) = ⇑f := fun δ hδ =>
    hf0 δ (by rw [Gamma_mem] at hδ; exact Gamma0_mem.mpr hδ.2.2.1)

  set h : UpperHalfPlane → ℂ := (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) with hh
  have hsm : ((1 + (ℓ : ℂ) ^ (k - 1)) • ⇑f) ∣[k] (γ : GL (Fin 2) ℝ)
      = (1 + (ℓ : ℂ) ^ (k - 1)) • ((⇑f) ∣[k] (γ : GL (Fin 2) ℝ)) :=
    ModularForm.SL_smul_slash k γ ⇑f _
  have hrw : (heckeT k ℓ ⇑f - (1 + (ℓ : ℂ) ^ (k - 1)) • ⇑f) ∣[k] (γ : GL (Fin 2) ℝ)
      = heckeT' k N ℓ h - (1 + (ℓ : ℂ) ^ (k - 1)) • h := by
    rw [heckeT_eq_heckeT' k hℓ hℓN hT, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      hsm, heckeT'_slash k hℓ hℓN hℓ1' hfΓ γ, ← sub_eq_add_neg]
  rw [hrw]

  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hper : Function.Periodic (h ∘ UpperHalfPlane.ofComplex) (N : ℝ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex (f := slashSIF f γ) (h := (N : ℝ))
      (by rw [strictPeriods_Gamma]; exact AddSubgroup.mem_zmultiples _)
    exact this
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := (ModularFormClass.holo f).slash k _
  have hbdd : IsBoundedAtImInfty h := ModularFormClass.bdd_at_infty_slash f γ
  have hlim := tendsto_atImInfty_of_periodic hN hper hhol hbdd
  have := tendsto_heckeT'_sub (N := N) k hℓ.ne_zero hlim
  rw [IsZeroAtImInfty, ZeroAtFilter]
  refine this.congr fun τ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

def cuspPart (f : ModularForm Γ₀(N) k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N]) :
    CuspForm Γ₀(N) k where
  toSlashInvariantForm :=
    (heckeTLin k hℓ (not_dvd_of_modEq_one hℓ hℓ1) f - (1 + (ℓ : ℂ) ^ (k - 1)) • f).1
  holo' := (heckeTLin k hℓ (not_dvd_of_modEq_one hℓ hℓ1) f - (1 + (ℓ : ℂ) ^ (k - 1)) • f).holo'
  zero_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact isZeroAtImInfty_slash f hℓ hℓ1 γ

theorem coe_cuspPart (f : ModularForm Γ₀(N) k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N]) :
    ⇑(cuspPart f hℓ hℓ1) = heckeT k ℓ ⇑f - (1 + (ℓ : ℂ) ^ (k - 1)) • ⇑f := rfl

theorem qCoeff_cuspPart (f : ModularForm Γ₀(N) k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N])
    (n : ℕ) :
    ModularFormClass.qCoeff (cuspPart f hℓ hℓ1) n
      = coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n
          - (1 + (ℓ : ℂ) ^ (k - 1)) * ModularFormClass.qCoeff f n := by
  have hℓN := not_dvd_of_modEq_one hℓ hℓ1
  have h1 : (1 : ℝ) ∈ (Γ₀(N)).strictPeriods := by simp
  have hT := ModularFormClass.qCoeff_heckeT f h1 hℓ.ne_zero n
  simp only [ModularFormClass.qCoeff] at hT ⊢
  have hsub := ModularForm.qExpansion_sub one_pos h1 (heckeTLin k hℓ hℓN f)
    ((1 + (ℓ : ℂ) ^ (k - 1)) • f)
  have hsmul := ModularForm.qExpansion_smul one_pos h1 (1 + (ℓ : ℂ) ^ (k - 1)) f
  rw [coe_cuspPart, ← coe_heckeTLin_apply k hℓ hℓN, ← ModularForm.IsGLPos.coe_smul, hsub,
    ModularForm.IsGLPos.coe_smul, hsmul, map_sub, map_smul, coe_heckeTLin_apply, hT, smul_eq_mul]

end Assembly

end EisensteinHeckeCongruence

end

open EisensteinHeckeCongruence in
theorem solution
    (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N']) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N') k, ∀ n : ℕ,
      ModularForm.coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n =
        (1 + (ℓ : ℂ) ^ (k - 1)) * ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n :=
  ⟨cuspPart f hℓ hℓ1, fun n => by rw [qCoeff_cuspPart]; ring⟩

end S_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one
end P2MW
export P2MW.S_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one (solution)
