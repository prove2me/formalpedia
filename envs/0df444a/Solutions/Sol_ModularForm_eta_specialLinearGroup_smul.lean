-- Prove2me | solution 1 for ModularForm.eta_specialLinearGroup_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/93ff08ec-fd9c-5d0e-b0c2-4fee2c08cf02

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Theorems.Thm_rademacher_phi_step
import Theorems.Thm_Complex_sqrt_mul_sqrt_eq_of_re_pos
import Theorems.Thm_ModularForm_eta_add_intCast
import Theorems.Thm_ModularForm_eta_modular_S_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_eta_specialLinearGroup_smul

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real

namespace DedekindEtaLaw

theorem radPhi_step (c r : ℕ) (hc : 0 < c) (hr : 0 < r) (a b d q : ℤ)
    (hrd : (r : ℤ) = q * c - d) (hdet : a * d - b * c = 1) :
    ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = ((q * a - b + c : ℤ) : ℚ) / r - 12 * dedekindSum c r + q - 3 :=
  rademacher_phi_step c r hc hr a b d q hrd hdet

theorem radPhi_base (a d : ℤ) :
    ((a + d : ℤ) : ℚ) / ((1 : ℕ) : ℚ) - 12 * dedekindSum d 1 = (a : ℚ) + d := by
  rw [dedekindSum_one_right]; push_cast; ring

theorem sqrt_mul_sqrt_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
    (h : u * v = -I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-I) * Complex.sqrt w :=
  Complex.sqrt_mul_sqrt_eq_of_re_pos hu hv hw h

lemma neg_I_mul_re (ζ : ℂ) : (-I * ζ).re = ζ.im := by simp

lemma eta_add_int (z : ℂ) (m : ℤ) : η (z + m) = cexp (π * I * m / 12) * η z := ModularForm.eta_add_intCast z m

lemma eta_T_zpow_smul (z : ℍ) (m : ℤ) :
    η (((ModularGroup.T ^ m • z : ℍ) : ℂ)) = cexp (π * I * m / 12) * η z := by
  rw [modular_T_zpow_smul, coe_vadd, add_comm]
  exact_mod_cast eta_add_int z m

lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [modular_S_smul]; simp [inv_neg]

lemma eta_S_smul (z : ℍ) : η (((ModularGroup.S • z : ℍ) : ℂ)) = Complex.sqrt (-I * z) * η z :=
  ModularForm.eta_modular_S_smul z

lemma sqrt_neg_I_eq_cexp : Complex.sqrt (-I) = cexp (-(π * I / 4)) := by
  rw [sqrt_eq_exp (neg_ne_zero.2 I_ne_zero), Complex.log_neg_I]
  congr 1
  ring

def phi (γ : SL(2, ℤ)) : ℚ :=
  ((γ 0 0 + γ 1 1 : ℤ) : ℚ) / (((γ 1 0 : ℤ).toNat : ℕ) : ℚ) - 12 * dedekindSum (γ 1 1) (γ 1 0 : ℤ).toNat

def Law (γ : SL(2, ℤ)) : Prop :=
  ∀ z : ℍ, η (((γ • z : ℍ) : ℂ)) =
    cexp (π * I / 12 * (phi γ : ℂ)) * Complex.sqrt (-I * ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ))) * η z

lemma det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe; rwa [Matrix.det_fin_two] at this

lemma law_of_c_eq_one (γ : SL(2, ℤ)) (hc : (γ 1 0 : ℤ) = 1) : Law γ := by
  intro z
  have hdet := det_eq γ
  rw [hc, mul_one] at hdet
  have hγ : γ = ModularGroup.T ^ (γ 0 0) * ModularGroup.S * ModularGroup.T ^ (γ 1 1) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
    linarith
  have hphi : (phi γ : ℂ) = (γ 0 0 : ℤ) + (γ 1 1 : ℤ) := by
    unfold phi
    rw [hc, Int.toNat_one, radPhi_base]
    push_cast; ring
  rw [hphi]
  conv_lhs => rw [hγ]
  rw [mul_smul, mul_smul, eta_T_zpow_smul, eta_S_smul, eta_T_zpow_smul, modular_T_zpow_smul, coe_vadd, hc]
  push_cast
  rw [mul_add (π * I / 12), Complex.exp_add]
  ring_nf

lemma law_step (γ : SL(2, ℤ)) (hc : 2 ≤ (γ 1 0 : ℤ))
    (ih : ∀ γ' : SL(2, ℤ), 0 < (γ' 1 0 : ℤ) → (γ' 1 0 : ℤ) < γ 1 0 → Law γ') : Law γ := by

  set a : ℤ := γ 0 0 with ha
  set b : ℤ := γ 0 1 with hb
  set c : ℤ := γ 1 0 with hcdef
  set d : ℤ := γ 1 1 with hd
  have hdet : a * d - b * c = 1 := det_eq γ
  have hc0 : 0 < c := by linarith

  set q : ℤ := -((-d) / c) with hq
  set r : ℤ := q * c - d with hr
  have hr_eq : r = (-d) % c := by
    have := Int.emod_add_mul_ediv (-d) c
    rw [hr, hq]; linarith
  have hr0 : 0 ≤ r := hr_eq ▸ Int.emod_nonneg _ hc0.ne'
  have hrc : r < c := hr_eq ▸ Int.emod_lt_of_pos _ hc0
  have hr_ne : r ≠ 0 := by
    intro h0

    have hcd : c ∣ d := ⟨q, by linarith [h0]⟩
    have : c ∣ 1 := by
      rw [← hdet]; exact Dvd.dvd.sub (Dvd.dvd.mul_left hcd a) (Dvd.intro_left _ rfl)
    have := Int.le_of_dvd one_pos this
    linarith
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_ne)

  let γ₁ : SL(2, ℤ) := ⟨!![q * a - b, a; r, c], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet⟩
  have hγ₁10 : (γ₁ 1 0 : ℤ) = r := rfl
  have hγ₁11 : (γ₁ 1 1 : ℤ) = c := rfl
  have hγ₁00 : (γ₁ 0 0 : ℤ) = q * a - b := rfl
  have hγ : γ = γ₁ * (ModularGroup.S * ModularGroup.T ^ q) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S, γ₁]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hcdef, ← hd, hr] <;> ring
  have ih₁ : Law γ₁ := ih γ₁ (hγ₁10 ▸ hrpos) (hγ₁10 ▸ hrc)
  intro z
  show η ((γ • z : ℍ) : ℂ) = cexp (π * I / 12 * (phi γ : ℂ)) * Complex.sqrt (-I * ((c : ℂ) * (z : ℂ) + d)) * η z

  set w : ℍ := ModularGroup.S • (ModularGroup.T ^ q • z) with hw
  have hwc : (w : ℂ) = -((z : ℂ) + q)⁻¹ := by
    rw [hw, coe_S_smul, modular_T_zpow_smul, coe_vadd]; push_cast; ring
  have hzq : (z : ℂ) + q ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact z.2.ne' this
  have hu : 0 < (-I * ((r : ℂ) * (w : ℂ) + c)).re := by
    rw [neg_I_mul_re]
    have : ((r : ℂ) * (w : ℂ) + c).im = r * w.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hrpos) w.2
  have hv : 0 < (-I * ((z : ℂ) + q)).re := by
    rw [neg_I_mul_re]; simpa using z.2
  have hw' : 0 < (-I * ((c : ℂ) * (z : ℂ) + d)).re := by
    rw [neg_I_mul_re]
    have : ((c : ℂ) * (z : ℂ) + d).im = c * z.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hc0) z.2
  have hdq : (d : ℂ) = q * c - r := by rw [hr]; push_cast; ring
  have hprod : (-I * ((r : ℂ) * (w : ℂ) + c)) * (-I * ((z : ℂ) + q)) = -I * (-I * ((c : ℂ) * (z : ℂ) + d)) := by
    have e1 : (-I * ((r : ℂ) * (w : ℂ) + c)) * (-I * ((z : ℂ) + q))
        = I ^ 2 * (((r : ℂ) * (w : ℂ) + c) * ((z : ℂ) + q)) := by ring
    have e2 : ((r : ℂ) * (w : ℂ) + c) * ((z : ℂ) + q) = -r + c * ((z : ℂ) + q) := by
      rw [hwc]; field_simp
    have e3 : -I * (-I * ((c : ℂ) * (z : ℂ) + d)) = I ^ 2 * ((c : ℂ) * (z : ℂ) + d) := by ring
    rw [e1, e2, e3, I_sq, hdq]
    ring

  have hL : (γ • z : ℍ) = γ₁ • w := by rw [hγ, mul_smul, mul_smul]
  have hηw : η (w : ℂ) = Complex.sqrt (-I * ((z : ℂ) + q)) * (cexp (π * I * q / 12) * η z) := by
    rw [hw, eta_S_smul, eta_T_zpow_smul, modular_T_zpow_smul, coe_vadd]; push_cast; ring_nf
  rw [hL, ih₁ w, hγ₁10, hγ₁11, hηw]
  rw [show ∀ A B C D E : ℂ, A * B * (C * (D * E)) = A * D * (B * C) * E from fun _ _ _ _ _ => by ring,
    sqrt_mul_sqrt_eq hu hv hw' hprod, sqrt_neg_I_eq_cexp]

  have hstep := radPhi_step c.toNat r.toNat (by omega) (by omega) a b d q
    (by rw [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg hc0.le]) (by rw [Int.toNat_of_nonneg hc0.le]; exact hdet)
  rw [Int.toNat_of_nonneg hc0.le] at hstep
  have e0 : phi γ = ((a + d : ℤ) : ℚ) / ((c.toNat : ℕ) : ℚ) - 12 * dedekindSum d c.toNat := rfl
  have e1 : phi γ₁ = ((q * a - b + c : ℤ) : ℚ) / ((r.toNat : ℕ) : ℚ) - 12 * dedekindSum c r.toNat := rfl
  have hphi : (phi γ : ℂ) = (phi γ₁ : ℂ) + q - 3 := by
    rw [e0, e1, hstep]; push_cast; ring
  rw [hphi, show π * I / 12 * ((phi γ₁ : ℂ) + q - 3) = π * I / 12 * (phi γ₁ : ℂ) + π * I * q / 12 + -(π * I / 4) by ring,
    Complex.exp_add, Complex.exp_add]
  ring

theorem law (γ : SL(2, ℤ)) (hc : 0 < (γ 1 0 : ℤ)) : Law γ := by
  suffices h : ∀ n : ℕ, ∀ γ : SL(2, ℤ), 0 < (γ 1 0 : ℤ) → (γ 1 0 : ℤ).toNat = n → Law γ from
    h _ γ hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro γ hc hn
    rcases lt_or_ge (γ 1 0 : ℤ) 2 with h1 | h2
    · exact law_of_c_eq_one γ (by omega)
    · exact law_step γ h2 fun γ' h' hlt => ihn _ (by omega) γ' h' rfl

end DedekindEtaLaw

end

theorem solution (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (z : UpperHalfPlane) : ModularForm.eta ((γ • z : UpperHalfPlane) : ℂ) = Complex.exp (Real.pi * Complex.I / 12 * (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) / ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℕ) : ℚ) - 12 * dedekindSum ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℚ) : ℂ)) * Complex.sqrt (-Complex.I * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (z : ℂ) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ))) * ModularForm.eta z :=
  DedekindEtaLaw.law γ hc z

end S_ModularForm_eta_specialLinearGroup_smul
end P2MW
export P2MW.S_ModularForm_eta_specialLinearGroup_smul (solution)
