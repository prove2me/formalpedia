-- Prove2me | solution 1 for ModularCurve.veluQuotient_nonToricSlotSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/66476d45-8501-5019-b6c5-237283281f83

import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_ModularCurve_TateSlots
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateB twelve_mul_tateB tateA4 tateA6 coeff_tateA4 coeff_tateA6 coeff_zero_tateA4 coeff_one_tateA4 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ instIsElliptic_tateLaurent qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg qTwist qTwist_coeff tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst nonToricPoint nonToricSlotSet tateBase nonToricPoint_fst nonToricPoint_snd tateUnivCurve_a₁ tateUnivCurve_a₂ tateUnivCurve_a₃ tateUnivCurve_a₄ instIsElliptic_tateBase"
p2m_open "ModularCurve"

def tateC (d : ℕ) : ℤ := ((d : ℤ) ^ 5 - (d : ℤ) ^ 3) / 12

def tateUnivEven (φ : ℕ → ℤ) : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then 0
  else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then φ (e 0 - e 1) else 0)
  else (if e 1 - e 0 ∣ e 1 then φ (e 1 - e 0) else 0)

def tateUnivT : MvPowerSeries (Fin 2) ℤ := tateUnivEven fun n => (n : ℤ) ^ 3

def tateUnivW : MvPowerSeries (Fin 2) ℤ := tateUnivEven tateC

def tateTheta (f : MvPowerSeries (Fin 2) ℤ) : MvPowerSeries (Fin 2) ℤ := fun e =>
  ((e 0 : ℤ) - e 1) * f e

section SlotSubstAPI

variable (K : Type*) [CommRing K]

theorem hasSubst_slotFamily (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries.HasSubst (slotFamily K p c j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  · show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp), mul_zero]

def slotHom (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries (Fin 2) ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (MvPowerSeries.substAlgHom (hasSubst_slotFamily K p c j hj hjp)).toRingHom

theorem slotHom_apply (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    slotHom K p c j hj hjp f = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) := by
  simp only [slotHom, slotSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPowerSeries.substAlgHom_apply]

end SlotSubstAPI

theorem two_mul_choose_two_succ (m : ℕ) : 2 * (m + 1).choose 2 = (m + 1) * m := by
  have h2 : 2 ∣ (m + 1) * m := by
    rw [mul_comm]
    exact (Nat.even_mul_succ_self m).two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' h2]

theorem twelve_mul_tateC (d : ℕ) : 12 * tateC d = (d : ℤ) ^ 5 - (d : ℤ) ^ 3 := by
  have key : (d : ℤ) ^ 5 - (d : ℤ) ^ 3 =
      12 * (7 * tateB d - 4 * (d : ℤ) ^ 5 - 3 * (d : ℤ) ^ 3) := by
    linear_combination (-7 : ℤ) * twelve_mul_tateB d
  rw [tateC, key, Int.mul_ediv_cancel_left _ (by norm_num : (12 : ℤ) ≠ 0)]

theorem tateB_eq_pow_add_tateC (d : ℕ) : tateB d = (d : ℤ) ^ 3 + 7 * tateC d := by
  have h1 := twelve_mul_tateB d
  have h2 := twelve_mul_tateC d
  linarith

theorem coeff_tateTheta (f : MvPowerSeries (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (tateTheta f) = ((e 0 : ℤ) - (e 1 : ℤ)) * MvPowerSeries.coeff e f :=
  rfl

theorem tateTheta_zero : tateTheta 0 = 0 := by
  ext e
  simp only [coeff_tateTheta, map_zero, mul_zero]

theorem tateTheta_add (f g : MvPowerSeries (Fin 2) ℤ) :
    tateTheta (f + g) = tateTheta f + tateTheta g := by
  ext e
  rw [map_add, coeff_tateTheta, coeff_tateTheta, coeff_tateTheta, map_add, mul_add]

theorem tateTheta_mul (f g : MvPowerSeries (Fin 2) ℤ) :
    tateTheta (f * g) = f * tateTheta g + tateTheta f * g := by
  ext e
  rw [map_add, coeff_tateTheta, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun uv huv => ?_
  have huv' : uv.1 + uv.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have h0 : (e 0 : ℤ) = (uv.1 0 : ℤ) + (uv.2 0 : ℤ) := by
    rw [← huv']; push_cast [Finsupp.add_apply]; ring
  have h1 : (e 1 : ℤ) = (uv.1 1 : ℤ) + (uv.2 1 : ℤ) := by
    rw [← huv']; push_cast [Finsupp.add_apply]; ring
  rw [coeff_tateTheta, coeff_tateTheta, h0, h1]
  ring

theorem tateTheta_eq_zero (f : MvPowerSeries (Fin 2) ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, e 0 ≠ e 1 → MvPowerSeries.coeff e f = 0) : tateTheta f = 0 := by
  ext e
  simp only [coeff_tateTheta, map_zero]
  by_cases h : e 0 = e 1
  · rw [h, sub_self, zero_mul]
  · rw [hf e h, mul_zero]

theorem tateTheta_one : tateTheta (1 : MvPowerSeries (Fin 2) ℤ) = 0 := by
  refine tateTheta_eq_zero 1 fun e he => ?_
  have h0 : e ≠ 0 := by rintro rfl; exact he rfl
  rw [MvPowerSeries.coeff_one, if_neg h0]

theorem tateTheta_natCast (n : ℕ) : tateTheta (n : MvPowerSeries (Fin 2) ℤ) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact tateTheta_zero
  | succ m ih =>
    have hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 2) ℤ) = (m : MvPowerSeries (Fin 2) ℤ) + 1 := by
      push_cast; ring
    rw [hc, tateTheta_add, ih, tateTheta_one, zero_add]

theorem tateTheta_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    tateTheta (OfNat.ofNat n : MvPowerSeries (Fin 2) ℤ) = 0 := by
  exact_mod_cast tateTheta_natCast n

theorem tateTheta_sq (f : MvPowerSeries (Fin 2) ℤ) :
    tateTheta (f ^ 2) = 2 * f * tateTheta f := by
  rw [sq, tateTheta_mul]; ring

theorem tateTheta_cube (f : MvPowerSeries (Fin 2) ℤ) :
    tateTheta (f ^ 3) = 3 * f ^ 2 * tateTheta f := by
  rw [show f ^ 3 = f ^ 2 * f by ring, tateTheta_mul, tateTheta_sq]; ring

theorem tateTheta_tateUnivA4 : tateTheta tateUnivA4 = 0 :=
  tateTheta_eq_zero _ fun e he => by
    simp only [MvPowerSeries.coeff_apply, tateUnivA4, if_neg he]

theorem tateTheta_tateUnivA6 : tateTheta tateUnivA6 = 0 :=
  tateTheta_eq_zero _ fun e he => by
    simp only [MvPowerSeries.coeff_apply, tateUnivA6, if_neg he]

theorem tateUnivCurve_b₂ : tateUnivCurve.b₂ = 1 := by
  simp [WeierstrassCurve.b₂, tateUnivCurve_a₁, tateUnivCurve_a₂]

theorem tateUnivCurve_b₄ : tateUnivCurve.b₄ = 2 * tateUnivA4 := by
  simp [WeierstrassCurve.b₄, tateUnivCurve_a₁, tateUnivCurve_a₃, tateUnivCurve_a₄]

theorem coeff_tateTheta_iterate (k : ℕ) (f : MvPowerSeries (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (tateTheta^[k] f) =
      ((e 0 : ℤ) - (e 1 : ℤ)) ^ k * MvPowerSeries.coeff e f := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ m ih => rw [Function.iterate_succ_apply', coeff_tateTheta, ih, pow_succ]; ring

theorem tateTheta_tateUnivX : tateTheta tateUnivX = 2 * tateUnivY + tateUnivX := by
  ext e
  rw [coeff_tateTheta, map_add, two_mul, map_add]
  simp only [MvPowerSeries.coeff_apply, tateUnivX, tateUnivY]
  rcases lt_trichotomy (e 0) (e 1) with h | h | h
  · rw [if_neg h.ne, if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h.le)]
    by_cases hd : e 1 - e 0 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 1 - e 0 = m + 1 := ⟨e 1 - e 0 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 1 : ℤ) - (e 0 : ℤ) := by
        have h' : ((e 1 - e 0 : ℕ) : ℤ) = (e 1 : ℤ) - (e 0 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      have hch : (2 : ℤ) * (((m + 1 + 1).choose 2 : ℕ) : ℤ) =
          ((m : ℤ) + 1 + 1) * ((m : ℤ) + 1) := by
        exact_mod_cast two_mul_choose_two_succ (m + 1)
      push_cast
      linear_combination hch + ((m : ℤ) + 1) * hc
    · rw [if_neg hd, if_neg hd]
      ring
  · rw [if_pos h, if_pos h, h, sub_self, zero_mul]
    ring
  · rw [if_neg h.ne', if_neg h.ne', if_pos h, if_pos h]
    by_cases hd : e 0 - e 1 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 0 - e 1 = m + 1 := ⟨e 0 - e 1 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 0 : ℤ) - (e 1 : ℤ) := by
        have h' : ((e 0 - e 1 : ℕ) : ℤ) = (e 0 : ℤ) - (e 1 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      have hch : (2 : ℤ) * (((m + 1).choose 2 : ℕ) : ℤ) = ((m : ℤ) + 1) * (m : ℤ) := by
        exact_mod_cast two_mul_choose_two_succ m
      push_cast
      linear_combination -hch - ((m : ℤ) + 1) * hc
    · rw [if_neg hd, if_neg hd]
      ring

theorem tateTheta_tateTheta_tateUnivX : tateTheta (tateTheta tateUnivX) = tateUnivT := by
  ext e
  rw [coeff_tateTheta, coeff_tateTheta]
  simp only [MvPowerSeries.coeff_apply, tateUnivX, tateUnivT, tateUnivEven]
  rcases lt_trichotomy (e 0) (e 1) with h | h | h
  · rw [if_neg h.ne, if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h.le)]
    by_cases hd : e 1 - e 0 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 1 - e 0 = m + 1 := ⟨e 1 - e 0 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 1 : ℤ) - (e 0 : ℤ) := by
        have h' : ((e 1 - e 0 : ℕ) : ℤ) = (e 1 : ℤ) - (e 0 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      push_cast
      linear_combination (((m : ℤ) + 1) * (((e 0 : ℤ) - (e 1 : ℤ)) - (m : ℤ) - 1)) * hc
    · rw [if_neg hd, if_neg hd]
      ring
  · rw [if_pos h, if_pos h, h, sub_self, zero_mul]
  · rw [if_neg h.ne', if_neg h.ne', if_pos h, if_pos h]
    by_cases hd : e 0 - e 1 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 0 - e 1 = m + 1 := ⟨e 0 - e 1 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 0 : ℤ) - (e 1 : ℤ) := by
        have h' : ((e 0 - e 1 : ℕ) : ℤ) = (e 0 : ℤ) - (e 1 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      push_cast
      linear_combination (-(((m : ℤ) + 1)) * (((e 0 : ℤ) - (e 1 : ℤ)) + (m : ℤ) + 1)) * hc
    · rw [if_neg hd, if_neg hd]
      ring

theorem tateTheta_iterate_sub_tateUnivX :
    tateTheta^[4] tateUnivX - tateTheta^[2] tateUnivX = 12 * tateUnivW := by
  have hsm : (12 : MvPowerSeries (Fin 2) ℤ) * tateUnivW = (12 : ℤ) • tateUnivW := by
    rw [zsmul_eq_mul]
    norm_num
  rw [hsm]
  ext e
  rw [map_sub, coeff_tateTheta_iterate, coeff_tateTheta_iterate, map_smul, smul_eq_mul]
  simp only [MvPowerSeries.coeff_apply, tateUnivX, tateUnivW, tateUnivEven]
  rcases lt_trichotomy (e 0) (e 1) with h | h | h
  · rw [if_neg h.ne, if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h.le)]
    by_cases hd : e 1 - e 0 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 1 - e 0 = m + 1 := ⟨e 1 - e 0 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 1 : ℤ) - (e 0 : ℤ) := by
        have h' : ((e 1 - e 0 : ℕ) : ℤ) = (e 1 : ℤ) - (e 0 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      have htc := twelve_mul_tateC (m + 1)
      push_cast at htc ⊢
      linear_combination -htc + (((m : ℤ) + 1) * (((e 0 : ℤ) - (e 1 : ℤ)) - (m : ℤ) - 1) *
        ((((e 0 : ℤ) - (e 1 : ℤ)) ^ 2 + ((m : ℤ) + 1) ^ 2 - 1))) * hc
    · rw [if_neg hd, if_neg hd]
      ring
  · rw [if_pos h, if_pos h, h, sub_self]
    norm_num
  · rw [if_neg h.ne', if_neg h.ne', if_pos h, if_pos h]
    by_cases hd : e 0 - e 1 ∣ e 1
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, hm⟩ : ∃ m, e 0 - e 1 = m + 1 := ⟨e 0 - e 1 - 1, by omega⟩
      rw [hm]
      have hc : ((m : ℤ) + 1) = (e 0 : ℤ) - (e 1 : ℤ) := by
        have h' : ((e 0 - e 1 : ℕ) : ℤ) = (e 0 : ℤ) - (e 1 : ℤ) := Nat.cast_sub h.le
        rw [hm] at h'
        push_cast at h'
        exact h'
      have htc := twelve_mul_tateC (m + 1)
      push_cast at htc ⊢
      linear_combination -htc - (((m : ℤ) + 1) * (((e 0 : ℤ) - (e 1 : ℤ)) + (m : ℤ) + 1) *
        ((((e 0 : ℤ) - (e 1 : ℤ)) ^ 2 + ((m : ℤ) + 1) ^ 2 - 1))) * hc
    · rw [if_neg hd, if_neg hd]
      ring

theorem tateTheta_tateUnivX_ne_zero : tateTheta tateUnivX ≠ 0 := by
  intro hzero
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hzero
  rw [coeff_tateTheta, map_zero (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)),
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at h
  norm_num [MvPowerSeries.coeff_apply, tateUnivX, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at h

private theorem tateUniv_equation (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    tateUnivY ^ 2 + tateUnivX * tateUnivY =
      tateUnivX ^ 3 + tateUnivA4 * tateUnivX + tateUnivA6 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  have h1 : tateUnivCurve.toAffine.a₁ = 1 := rfl
  have h2 : tateUnivCurve.toAffine.a₂ = 0 := rfl
  have h3 : tateUnivCurve.toAffine.a₃ = 0 := rfl
  have h4 : tateUnivCurve.toAffine.a₄ = tateUnivA4 := rfl
  have h6 : tateUnivCurve.toAffine.a₆ = tateUnivA6 := rfl
  rw [h1, h2, h3, h4, h6] at hE
  linear_combination hE

theorem tateTheta_tateUnivY_of_equation
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    tateTheta tateUnivY = 3 * tateUnivX ^ 2 + tateUnivA4 - tateUnivY := by
  have hEq := tateUniv_equation hE
  have hθE := congrArg tateTheta hEq
  simp only [tateTheta_add, tateTheta_mul, tateTheta_sq, tateTheta_cube,
    tateTheta_tateUnivA4, tateTheta_tateUnivA6, zero_mul, add_zero] at hθE
  have key : tateTheta tateUnivX *
      (tateTheta tateUnivY + tateUnivY - (3 * tateUnivX ^ 2 + tateUnivA4)) = 0 := by
    linear_combination hθE + tateTheta tateUnivY * tateTheta_tateUnivX
  rcases mul_eq_zero.mp key with hk | hk
  · exact absurd hk tateTheta_tateUnivX_ne_zero
  · linear_combination hk

theorem tateTheta_sq_tateUnivX_of_equation
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    tateTheta (tateTheta tateUnivX) = 6 * tateUnivX ^ 2 + tateUnivX + 2 * tateUnivA4 := by
  have hY := tateTheta_tateUnivY_of_equation hE
  rw [tateTheta_tateUnivX, tateTheta_add, tateTheta_mul, tateTheta_ofNat, hY,
    tateTheta_tateUnivX]
  ring

theorem veluT_tateUniv (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    tateUnivCurve.veluT tateUnivX tateUnivY = tateUnivT := by
  rw [WeierstrassCurve.veluT_eq, tateUnivCurve_b₂, tateUnivCurve_b₄]
  linear_combination tateTheta_tateTheta_tateUnivX - tateTheta_sq_tateUnivX_of_equation hE

theorem veluW_tateUniv (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    tateUnivCurve.veluW tateUnivX tateUnivY = tateUnivW := by
  have h12 : (12 : MvPowerSeries (Fin 2) ℤ) ≠ 0 := by
    intro hc
    have h' := congrArg MvPowerSeries.constantCoeff hc
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hθX := tateTheta_tateUnivX
  have hTeq := tateTheta_sq_tateUnivX_of_equation hE
  have h3 : tateTheta (tateTheta (tateTheta tateUnivX)) =
      tateTheta tateUnivX * (12 * tateUnivX + 1) := by
    rw [hTeq, tateTheta_add, tateTheta_add, tateTheta_mul, tateTheta_mul, tateTheta_sq,
      tateTheta_ofNat, tateTheta_ofNat, tateTheta_tateUnivA4]
    ring
  have h4 : tateTheta (tateTheta (tateTheta (tateTheta tateUnivX))) =
      12 * tateTheta tateUnivX ^ 2 +
        tateTheta (tateTheta tateUnivX) * (12 * tateUnivX + 1) := by
    rw [h3, tateTheta_mul, tateTheta_add, tateTheta_mul, tateTheta_ofNat, tateTheta_one]
    ring
  have hW := tateTheta_iterate_sub_tateUnivX
  rw [show tateTheta^[4] tateUnivX =
        tateTheta (tateTheta (tateTheta (tateTheta tateUnivX))) from rfl,
    show tateTheta^[2] tateUnivX = tateTheta (tateTheta tateUnivX) from rfl] at hW
  apply mul_left_cancel₀ h12
  simp only [WeierstrassCurve.veluW, WeierstrassCurve.veluU]
  have hgy : tateUnivCurve.veluGy tateUnivX tateUnivY = -(2 * tateUnivY + tateUnivX) := by
    simp only [WeierstrassCurve.veluGy, tateUnivCurve_a₁, tateUnivCurve_a₃, one_mul, add_zero]
  rw [hgy, WeierstrassCurve.veluT_eq, tateUnivCurve_b₂, tateUnivCurve_b₄]
  linear_combination hW - h4 -
    (12 * (tateTheta tateUnivX + 2 * tateUnivY + tateUnivX)) * hθX -
    (12 * tateUnivX) * hTeq

section SpecS0

def reidxLineSet (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter fun e => a * e.1 + b * e.2 = N

def toFin2 (e : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e.1, e.2]

@[scoped simp] theorem toFin2_apply_zero (e : ℕ × ℕ) : toFin2 e 0 = e.1 := by simp [toFin2]

@[scoped simp] theorem toFin2_apply_one (e : ℕ × ℕ) : toFin2 e 1 = e.2 := by simp [toFin2]

theorem toFin2_injective : Function.Injective toFin2 := by
  intro x y h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [toFin2_apply_zero, toFin2_apply_one] at h0 h1
  exact Prod.ext h0 h1

theorem toFin2_pair (d : Fin 2 →₀ ℕ) : toFin2 (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact toFin2_apply_zero _
  · exact toFin2_apply_one _

theorem mem_reidxLineSet {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) {e : ℕ × ℕ} :
    e ∈ reidxLineSet a b N ↔ a * e.1 + b * e.2 = N := by
  simp only [reidxLineSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h
  have h1 : e.1 ≤ a * e.1 := Nat.le_mul_of_pos_left _ ha
  have h2 : e.2 ≤ b * e.2 := Nat.le_mul_of_pos_left _ hb
  exact ⟨Nat.lt_succ_of_le (h1.trans (le_of_le_of_eq (Nat.le_add_right _ _) h)),
    Nat.lt_succ_of_le (h2.trans (le_of_le_of_eq (Nat.le_add_left _ _) h))⟩

end SpecS0

section SpecS1

theorem prod_pow_fin_two {M : Type*} [CommMonoid M] (a : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => a s ^ n) = a 0 ^ (d 0) * a 1 ^ (d 1) := by
  rw [Finsupp.prod_fintype d (fun s n => a s ^ n) fun _ => pow_zero _, Fin.prod_univ_two]

theorem coeff_subst_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A B : PowerSeries S) (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) (f : MvPowerSeries (Fin 2) R) (N : ℕ) :
    PowerSeries.coeff N (MvPowerSeries.subst ![A, B] f : PowerSeries S) =
      ∑ e ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        MvPowerSeries.coeff (toFin2 e) f • PowerSeries.coeff N (A ^ e.1 * B ^ e.2) := by
  have ha : MvPowerSeries.HasSubst (![A, B] : Fin 2 → PowerSeries S) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      fin_cases s
      · exact hA
      · exact hB
  have key : ∀ d : Fin 2 →₀ ℕ, ¬(d 0 ≤ N ∧ d 1 ≤ N) →
      PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0 := by
    intro d hd
    obtain ⟨A', hA'⟩ := PowerSeries.X_dvd_iff.mpr hA
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.mpr hB
    rw [hA', hB', mul_pow, mul_pow, mul_mul_mul_comm, ← _root_.pow_add, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega)]
  change MvPowerSeries.coeff (Finsupp.single () N) (MvPowerSeries.subst ![A, B] f) = _
  rw [MvPowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _
      (s := (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).image toFin2)]
  · rw [Finset.sum_image fun x _ y _ h => toFin2_injective h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff (toFin2 e) f •
        PowerSeries.coeff N (A ^ (toFin2 e 0) * B ^ (toFin2 e 1)) = _
    rw [toFin2_apply_zero, toFin2_apply_one]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨(d 0, d 1), ?_, toFin2_pair d⟩
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    by_contra hbox
    apply hd
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff d f • PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0
    rw [key d (by omega), smul_zero]

end SpecS1

section SpecS2

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      ∑ e ∈ reidxLineSet j (p - j) N,
        ((f (toFin2 e) : ℤ) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) := by
  have hA : PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  have hB : PowerSeries.constantCoeff
      (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp),
      mul_zero]
  rw [slotSubst, slotFamily, coeff_subst_pair _ _ hA hB, reidxLineSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← map_mul,
    ← _root_.pow_add, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : j * e.1 + (p - j) * e.2 = N
  · rw [if_pos h.symm, if_pos h, Algebra.smul_def, eq_intCast, MvPowerSeries.coeff_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  · rw [if_neg (Ne.symm h), if_neg h, smul_zero]

end SpecS2

section SpecS3

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      if p ∣ N then ((PowerSeries.coeff (N / p) g : ℤ) : K) else 0 := by
  have hpj : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hline : ∀ m : ℕ, j * m + (p - j) * m = p * m := fun m => by
    rw [← add_mul, Nat.add_sub_cancel' hjp.le]
  rw [coeff_slotSubst K p c j hj hjp]
  by_cases hN : p ∣ N
  · obtain ⟨m, rfl⟩ := hN
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p),
      Finset.sum_eq_single_of_mem (m, m) ((mem_reidxLineSet hj hpj).mpr (hline m))]
    · rw [hf, toFin2_apply_zero, toFin2_apply_one, if_pos rfl, ← mul_pow, mul_inv_cancel, one_pow,
        Units.val_one, mul_one]
    · intro e he hne
      have h := (mem_reidxLineSet hj hpj).mp he
      rw [hf, toFin2_apply_zero, toFin2_apply_one]
      by_cases h01 : e.1 = e.2
      · exfalso
        refine hne (Prod.ext ?_ ?_)
        · change e.1 = m
          rw [h01, hline e.2] at h
          exact h01.trans (Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h)
        · change e.2 = m
          rw [h01, hline e.2] at h
          exact Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h
      · rw [if_neg h01, Int.cast_zero, zero_mul]
  · rw [if_neg hN]
    refine Finset.sum_eq_zero fun e he => ?_
    have h := (mem_reidxLineSet hj hpj).mp he
    rw [hf, toFin2_apply_zero, toFin2_apply_one]
    by_cases h01 : e.1 = e.2
    · exfalso
      rw [h01, hline e.2] at h
      exact hN ⟨e.2, h.symm⟩
    · rw [if_neg h01, Int.cast_zero, zero_mul]

theorem ofPowerSeries_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) = qExpand K p (laurentOfInt K g) := by
  ext n
  by_cases hpn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    rw [qExpand_coeff_mul, laurentOfInt_apply]
    rcases lt_or_ge k 0 with hk | hk
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _
        (mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos p) hk)]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [show (p : ℤ) * (m : ℤ) = ((p * m : ℕ) : ℤ) by push_cast; rfl,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, coeff_slotSubst_diag K p c j hj hjp f g hf,
        if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p), eq_intCast]
  · rw [qExpand_coeff_of_not_dvd p _ hpn]
    rcases lt_or_ge n 0 with hn | hn
    · exact ofPowerSeries_coeff_of_neg _ hn
    · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_slotSubst_diag K p c j hj hjp f g hf,
        if_neg (fun h => hpn (Int.natCast_dvd_natCast.mpr h))]

theorem ofPowerSeries_slotSubst_tateUnivA4 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA4) = (tateBase K p).a₄ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA4 tateA4 fun _ => rfl).trans rfl

theorem ofPowerSeries_slotSubst_tateUnivA6 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA6) = (tateBase K p).a₆ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA6 tateA6 fun _ => rfl).trans rfl

end SpecS3

section SpecS4

variable (K : Type*) [CommRing K]

theorem veluT_map_ringHom {R A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R)
    (φ : R →+* A) (x y : R) : (W.map φ).veluT (φ x) (φ y) = φ (W.veluT x y) := by
  simp only [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, map_sub, map_mul, map_add, map_neg, map_pow, map_ofNat]

theorem veluW_map_ringHom {R A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R)
    (φ : R →+* A) (x y : R) : (W.map φ).veluW (φ x) (φ y) = φ (W.veluW x y) := by
  simp only [WeierstrassCurve.veluW, WeierstrassCurve.veluU, WeierstrassCurve.veluT,
    WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, map_sub, map_mul,
    map_add, map_neg, map_pow, map_ofNat]

theorem tateUnivCurve_map_slotHom (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) : tateUnivCurve.map (slotHom K p c j hj hjp) = tateBase K p := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · change slotHom K p c j hj hjp 1 = qExpand K p (laurentOfInt K 1)
    simp only [map_one]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp tateUnivA4 = (tateBase K p).a₄
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA4 K p c j hj hjp]
  · change slotHom K p c j hj hjp tateUnivA6 = (tateBase K p).a₆
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA6 K p c j hj hjp]

theorem veluT_nonToricPoint (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hT : tateUnivCurve.veluT tateUnivX tateUnivY = tateUnivT) :
    (tateBase K p).veluT (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 =
      HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivT) := by
  rw [nonToricPoint_fst, nonToricPoint_snd, ← slotHom_apply K p c j hj hjp,
    ← slotHom_apply K p c j hj hjp, ← slotHom_apply K p c j hj hjp,
    ← tateUnivCurve_map_slotHom K p c j hj hjp, veluT_map_ringHom, hT]

theorem veluW_nonToricPoint (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hW : tateUnivCurve.veluW tateUnivX tateUnivY = tateUnivW) :
    (tateBase K p).veluW (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 =
      HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivW) := by
  rw [nonToricPoint_fst, nonToricPoint_snd, ← slotHom_apply K p c j hj hjp,
    ← slotHom_apply K p c j hj hjp, ← slotHom_apply K p c j hj hjp,
    ← tateUnivCurve_map_slotHom K p c j hj hjp, veluW_map_ringHom, hW]

end SpecS4

section SpecS5

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst_eq_zero_of_lt (p : ℕ) (c : Kˣ) (k : ℕ) (h2k : 2 * k ≤ p)
    (f : MvPowerSeries (Fin 2) ℤ) (N : ℕ) (hN : 0 < N) (hNk : N < k) :
    PowerSeries.coeff N (slotSubst K p c k f) = 0 := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le N) hNk
  have hkp : k < p := by omega
  rw [coeff_slotSubst K p c k hk hkp]
  refine Finset.sum_eq_zero fun e he => ?_
  exfalso
  have h := (mem_reidxLineSet hk (Nat.sub_pos_of_lt hkp)).mp he
  rcases Nat.eq_zero_or_pos e.1 with h1 | h1
  · rw [h1, mul_zero, zero_add] at h
    rcases Nat.eq_zero_or_pos e.2 with h2 | h2
    · rw [h2, mul_zero] at h
      omega
    · have h3 : p - k ≤ (p - k) * e.2 := Nat.le_mul_of_pos_right _ h2
      generalize (p - k) * e.2 = B at h h3
      omega
  · have h3 : k ≤ k * e.1 := Nat.le_mul_of_pos_right _ h1
    generalize k * e.1 = A at h h3
    generalize (p - k) * e.2 = B at h
    omega

theorem coeff_slotSubst_tateUnivX_self (p : ℕ) (c : Kˣ) (k : ℕ) (hk : 0 < k) (h2k : 2 * k < p) :
    PowerSeries.coeff k (slotSubst K p c k tateUnivX) = (c : K) := by
  have hkp : k < p := by omega
  have hX : tateUnivX (toFin2 (1, 0)) = 1 := by simp [tateUnivX]
  rw [coeff_slotSubst K p c k hk hkp, Finset.sum_eq_single_of_mem (1, 0)
    ((mem_reidxLineSet hk (Nat.sub_pos_of_lt hkp)).mpr (by simp))]
  · rw [hX, Int.cast_one, one_mul, pow_one, pow_zero, mul_one]
  · intro e he hne
    exfalso
    have h := (mem_reidxLineSet hk (Nat.sub_pos_of_lt hkp)).mp he
    rcases Nat.eq_zero_or_pos e.2 with h2 | h2
    · refine hne (Prod.ext ?_ h2)
      rw [h2, mul_zero, add_zero] at h
      exact Nat.eq_of_mul_eq_mul_left hk (h.trans (mul_one k).symm)
    · have h3 : p - k ≤ (p - k) * e.2 := Nat.le_mul_of_pos_right _ h2
      generalize (p - k) * e.2 = B at h h3
      generalize k * e.1 = A at h
      omega

theorem nonToricPoint_injOn [Nontrivial K] (p : ℕ) (u : ℕ → Kˣ) :
    Set.InjOn (fun k => nonToricPoint K p (u k) k) (Finset.Icc 1 (p / 2) : Set ℕ) := by
  intro k hk k' hk' h
  rw [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have hx : slotSubst K p (u k) k tateUnivX = slotSubst K p (u k') k' tateUnivX := by
    have h1 := congrArg Prod.fst h
    simp only [nonToricPoint_fst] at h1
    exact HahnSeries.ofPowerSeries_injective h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := congrArg (PowerSeries.coeff k) hx
    rw [coeff_slotSubst_tateUnivX_self K p (u k) k (by omega) (by omega),
      coeff_slotSubst_eq_zero_of_lt K p (u k') k' (by omega) tateUnivX k (by omega) hlt] at h1
    exact (u k).ne_zero h1
  · have h1 := congrArg (PowerSeries.coeff k') hx
    rw [coeff_slotSubst_eq_zero_of_lt K p (u k) k (by omega) tateUnivX k' (by omega) hlt,
      coeff_slotSubst_tateUnivX_self K p (u k') k' (by omega) (by omega)] at h1
    exact (u k').ne_zero h1.symm

open scoped Classical in

theorem sum_nonToricSlotSet (p : ℕ) (ζ : Kˣ) (b : ℕ)
    (g : LaurentSeries K × LaurentSeries K → LaurentSeries K) :
    ∑ P ∈ nonToricSlotSet K p ζ b, g P =
      ∑ k ∈ Finset.Icc 1 (p / 2), g (nonToricPoint K p (ζ ^ (b * k)) k) := by
  cases subsingleton_or_nontrivial K with
  | inl h => exact Subsingleton.elim _ _
  | inr h => exact Finset.sum_image (nonToricPoint_injOn K p fun k => ζ ^ (b * k))

end SpecS5

section SpecS6

def c1X : PowerSeries ℚ := slotSubst ℚ 3 1 1 tateUnivX

def c1A4 : PowerSeries ℚ := slotSubst ℚ 3 1 1 tateUnivA4

theorem c1X_coeff (N : ℕ) :
    PowerSeries.coeff N c1X = ((∑ e ∈ reidxLineSet 1 2 N, tateUnivX (toFin2 e) : ℤ) : ℚ) := by
  rw [c1X, coeff_slotSubst ℚ 3 1 1 Nat.one_pos (by norm_num) tateUnivX N, Int.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [one_pow, inv_one, one_pow, mul_one, Units.val_one, mul_one]

theorem c1A4_coeff (N : ℕ) :
    PowerSeries.coeff N c1A4 = if 3 ∣ N then ((PowerSeries.coeff (N / 3) tateA4 : ℤ) : ℚ) else 0 :=
  coeff_slotSubst_diag ℚ 3 1 1 Nat.one_pos (by norm_num) tateUnivA4 tateA4 (fun _ => rfl) N

theorem c1X_coeff_zero : PowerSeries.coeff 0 c1X = 0 := by
  rw [c1X_coeff, show (∑ e ∈ reidxLineSet 1 2 0, tateUnivX (toFin2 e)) = 0 from by decide +kernel,
    Int.cast_zero]

theorem c1X_coeff_one : PowerSeries.coeff 1 c1X = 1 := by
  rw [c1X_coeff, show (∑ e ∈ reidxLineSet 1 2 1, tateUnivX (toFin2 e)) = 1 from by decide +kernel,
    Int.cast_one]

theorem c1X_coeff_two : PowerSeries.coeff 2 c1X = 3 := by
  rw [c1X_coeff, show (∑ e ∈ reidxLineSet 1 2 2, tateUnivX (toFin2 e)) = 3 from by decide +kernel]
  norm_num

theorem c1X_coeff_three : PowerSeries.coeff 3 c1X = 1 := by
  rw [c1X_coeff, show (∑ e ∈ reidxLineSet 1 2 3, tateUnivX (toFin2 e)) = 1 from by decide +kernel,
    Int.cast_one]

theorem c1X_coeff_four : PowerSeries.coeff 4 c1X = 7 := by
  rw [c1X_coeff, show (∑ e ∈ reidxLineSet 1 2 4, tateUnivX (toFin2 e)) = 7 from by decide +kernel]
  norm_num

theorem c1A4_coeff_zero : PowerSeries.coeff 0 c1A4 = 0 := by
  rw [c1A4_coeff, if_pos (dvd_zero 3), Nat.zero_div, coeff_zero_tateA4, Int.cast_zero]

theorem c1A4_coeff_one : PowerSeries.coeff 1 c1A4 = 0 := by
  rw [c1A4_coeff, if_neg (by decide)]

theorem c1A4_coeff_two : PowerSeries.coeff 2 c1A4 = 0 := by
  rw [c1A4_coeff, if_neg (by decide)]

theorem c1A4_coeff_three : PowerSeries.coeff 3 c1A4 = -5 := by
  rw [c1A4_coeff, if_pos (dvd_refl 3), Nat.div_self (by norm_num), coeff_one_tateA4]
  norm_num

theorem c1A4_coeff_four : PowerSeries.coeff 4 c1A4 = 0 := by
  rw [c1A4_coeff, if_neg (by decide)]

theorem c1_coeff_expand (N : ℕ) :
    PowerSeries.coeff N (6 * c1X ^ 2 + c1X + 2 * c1A4) =
      6 * (∑ k ∈ Finset.range N.succ, PowerSeries.coeff k c1X * PowerSeries.coeff (N - k) c1X) +
        PowerSeries.coeff N c1X + 2 * PowerSeries.coeff N c1A4 := by
  rw [show (6 : PowerSeries ℚ) = PowerSeries.C (6 : ℚ) from (map_ofNat _ 6).symm,
    show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from (map_ofNat _ 2).symm, map_add, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      PowerSeries.coeff i c1X * PowerSeries.coeff j c1X]

example : PowerSeries.coeff 1 (6 * c1X ^ 2 + c1X + 2 * c1A4) = 1 := by
  rw [c1_coeff_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    c1X_coeff_zero, c1X_coeff_one, c1A4_coeff_one]
  norm_num

example : PowerSeries.coeff 2 (6 * c1X ^ 2 + c1X + 2 * c1A4) = 9 := by
  rw [c1_coeff_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, c1X_coeff_zero, c1X_coeff_one, c1X_coeff_two, c1A4_coeff_two]
  norm_num

example : PowerSeries.coeff 3 (6 * c1X ^ 2 + c1X + 2 * c1A4) = 27 := by
  rw [c1_coeff_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, c1X_coeff_zero, c1X_coeff_one, c1X_coeff_two, c1X_coeff_three, c1A4_coeff_three]
  norm_num

example : PowerSeries.coeff 4 (6 * c1X ^ 2 + c1X + 2 * c1A4) = 73 := by
  rw [c1_coeff_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, c1X_coeff_zero, c1X_coeff_one, c1X_coeff_two, c1X_coeff_three, c1X_coeff_four,
    c1A4_coeff_four]
  norm_num

example : PowerSeries.coeff 3 tateA4 = -140 := by
  rw [coeff_tateA4, Nat.Prime.divisors Nat.prime_three, Finset.sum_pair (by decide)]
  norm_num

end SpecS6

section SpecS7

theorem c1_coeff_three : PowerSeries.coeff 3 (6 * c1X ^ 2 + c1X + 2 * c1A4) = 27 := by
  rw [c1_coeff_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, c1X_coeff_zero, c1X_coeff_one, c1X_coeff_two, c1X_coeff_three, c1A4_coeff_three]
  norm_num

theorem c1_tateA4_coeff_three : PowerSeries.coeff 3 tateA4 = -140 := by
  rw [coeff_tateA4, Nat.Prime.divisors Nat.prime_three, Finset.sum_pair (by decide)]
  norm_num

theorem c1_veluT_eq :
    (tateBase ℚ 3).veluT (nonToricPoint ℚ 3 1 1).1 (nonToricPoint ℚ 3 1 1).2 =
      HahnSeries.ofPowerSeries ℤ ℚ (6 * c1X ^ 2 + c1X + 2 * c1A4) := by
  have hb₂ : (tateBase ℚ 3).b₂ = 1 := by
    simp [tateBase, tateLaurent, WeierstrassCurve.b₂]
  have hb₄ : (tateBase ℚ 3).b₄ = 2 * (tateBase ℚ 3).a₄ := by
    simp [tateBase, tateLaurent, WeierstrassCurve.b₄]
  rw [WeierstrassCurve.veluT_eq, hb₂, hb₄, one_mul, nonToricPoint_fst,
    ← ofPowerSeries_slotSubst_tateUnivA4 ℚ 3 1 1 Nat.one_pos (by norm_num)]
  simp only [map_add, map_mul, map_pow, map_ofNat, c1X, c1A4]

theorem c1_veluTSum :
    (tateBase ℚ 3).veluTSum (nonToricSlotSet ℚ 3 1 0) =
      HahnSeries.ofPowerSeries ℤ ℚ (6 * c1X ^ 2 + c1X + 2 * c1A4) := by
  rw [WeierstrassCurve.veluTSum, sum_nonToricSlotSet]
  simp only [Nat.reduceDiv, Finset.Icc_self, Finset.sum_singleton, zero_mul, pow_zero]
  exact c1_veluT_eq

theorem c1_tateBase_a₄_coeff_three : (tateBase ℚ 3).a₄.coeff 3 = -5 := by
  change (qExpand ℚ 3 (laurentOfInt ℚ tateA4)).coeff ((3 : ℕ) * (1 : ℤ)) = -5
  rw [qExpand_coeff_mul, laurentOfInt_apply, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, coeff_one_tateA4, eq_intCast]
  norm_num

example : ((tateBase ℚ 3).veluT (nonToricPoint ℚ 3 1 1).1 (nonToricPoint ℚ 3 1 1).2).coeff 3 =
    27 := by
  rw [c1_veluT_eq, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    c1_coeff_three]

example : ((tateBase ℚ 3).veluQuotient (nonToricSlotSet ℚ 3 1 0)).a₄.coeff 3 = -140 := by
  rw [WeierstrassCurve.veluQuotient_a₄, HahnSeries.coeff_sub, c1_tateBase_a₄_coeff_three,
    c1_veluTSum, show (5 : LaurentSeries ℚ) = HahnSeries.C (5 : ℚ) from (map_ofNat _ 5).symm,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, c1_coeff_three]
  norm_num

example : (tateLaurent ℚ).a₄.coeff 3 = -140 := by
  rw [tateLaurent_a₄, laurentOfInt_apply, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, c1_tateA4_coeff_three, eq_intCast]
  norm_num

end SpecS7

section SpecS9

def c9core (e : ℕ × ℕ) : ℤ :=
  if e.1 = e.2 then (0 : ℤ)
  else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then ((e.1 - e.2 : ℕ) : ℤ) ^ 3 else 0)
  else (if e.2 - e.1 ∣ e.2 then ((e.2 - e.1 : ℕ) : ℤ) ^ 3 else 0)

def c9lhs (p N : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 (p / 2), ∑ e ∈ reidxLineSet k (p - k) N, c9core e

def c9rhs (p N : ℕ) : ℤ := ∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), ((d : ℕ) : ℤ) ^ 3

example : ∀ N ∈ Finset.range 13, c9lhs 3 N = c9rhs 3 N := by decide +kernel
example : ∀ N ∈ Finset.range 13, c9lhs 5 N = c9rhs 5 N := by decide +kernel
example : ∀ N ∈ Finset.range 11, c9lhs 7 N = c9rhs 7 N := by decide +kernel
example : ∀ N ∈ Finset.range 19, c9lhs 9 N = c9rhs 9 N := by decide +kernel

example : c9lhs 2 2 ≠ c9rhs 2 2 := by decide +kernel

example : c9rhs 3 3 = 27 := by decide +kernel

end SpecS9

section SpecS8

variable (K : Type*) [CommRing K]

theorem slotUnit_eq (p : ℕ) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b k N : ℕ) (e : ℕ × ℕ)
    (he : k * e.1 + (p - k) * e.2 = N) (hkp : k ≤ p) :
    (ζ ^ (b * k)) ^ e.1 * (ζ ^ (b * k))⁻¹ ^ e.2 = (ζ ^ b) ^ N := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkp
  rw [Nat.add_sub_cancel_left] at he
  subst he
  rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add,
    show b * (k * e.1 + m * e.2) + b * k * e.2 = b * k * e.1 + (k + m) * (b * e.2) by ring,
    pow_add, pow_mul ζ (k + m) (b * e.2), hζ, one_pow, mul_one]

theorem sum_slotSubst_tateUnivEven_of_core (φ : ℕ → ℤ) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : ζ ^ p = 1) (b : ℕ)
    (hcore : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 (p / 2), ∑ e ∈ reidxLineSet k (p - k) N,
        (if e.1 = e.2 then (0 : ℤ)
         else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then φ (e.1 - e.2) else 0)
         else (if e.2 - e.1 ∣ e.2 then φ (e.2 - e.1) else 0))) =
      ∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), φ d)
    (hsplit : ∀ N : ℕ, ∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), φ d =
      (∑ d ∈ N.divisors, φ d) - (if p ∣ N then ∑ d ∈ (N / p).divisors, φ d else 0)) :
    ∑ k ∈ Finset.Icc 1 (p / 2),
        HahnSeries.ofPowerSeries ℤ K (slotSubst K p (ζ ^ (b * k)) k (tateUnivEven φ)) =
      qTwist (ζ ^ b) (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)) -
        qExpand K p (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)) := by
  have hp0 : 0 < p := NeZero.pos p
  have hF : ∀ N : ℕ,
      (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)).coeff (N : ℤ) =
        ((∑ d ∈ N.divisors, φ d : ℤ) : K) := fun N => by
    rw [laurentOfInt_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, eq_intCast]
  have hFneg : ∀ n : ℤ, n < 0 →
      (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)).coeff n = 0 :=
    fun n hn => by
      rw [laurentOfInt_apply]
      exact ofPowerSeries_coeff_of_neg _ hn
  have hunit : ∀ N : ℕ, p ∣ N → (ζ ^ b) ^ N = 1 := by
    rintro N ⟨m, rfl⟩
    rw [← pow_mul, show b * (p * m) = p * (b * m) by ring, pow_mul, hζ, one_pow]
  ext n
  rw [HahnSeries.coeff_sum, HahnSeries.coeff_sub, qTwist_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · have h0 : ∑ k ∈ Finset.Icc 1 (p / 2), (HahnSeries.ofPowerSeries ℤ K
        (slotSubst K p (ζ ^ (b * k)) k (tateUnivEven φ))).coeff n = 0 :=
      Finset.sum_eq_zero fun k _ => ofPowerSeries_coeff_of_neg _ hn
    rw [h0, hFneg n hn, mul_zero, zero_sub]
    by_cases hpn : (p : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : m < 0 :=
        not_le.mp fun h => absurd hn (not_lt.mpr (mul_nonneg (Int.natCast_nonneg p) h))
      rw [qExpand_coeff_mul, hFneg m hm, neg_zero]
    · rw [qExpand_coeff_of_not_dvd p _ hpn, neg_zero]
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hLHS : ∑ k ∈ Finset.Icc 1 (p / 2), (HahnSeries.ofPowerSeries ℤ K
        (slotSubst K p (ζ ^ (b * k)) k (tateUnivEven φ))).coeff (N : ℤ) =
        (((ζ ^ b) ^ N : Kˣ) : K) *
          ((∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), φ d : ℤ) : K) := by
      rw [← hcore N, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hk0 : 0 < k := hk.1
      have hkp : k < p := lt_of_le_of_lt hk.2 (Nat.div_lt_self hp0 one_lt_two)
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_slotSubst K p _ k hk0 hkp, Int.cast_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [slotUnit_eq K p ζ hζ b k N e ((mem_reidxLineSet hk0 (Nat.sub_pos_of_lt hkp)).mp he)
        hkp.le, mul_comm]
      rfl
    rw [hLHS, hsplit N, zpow_natCast, hF N]
    by_cases hpN : p ∣ N
    · obtain ⟨m, rfl⟩ := hpN
      rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp0, hunit _ (dvd_mul_right p m),
        Units.val_one, one_mul, one_mul, Nat.cast_mul, qExpand_coeff_mul, hF m, Int.cast_sub]
    · rw [if_neg hpN, sub_zero,
        qExpand_coeff_of_not_dvd p _ (fun h => hpN (Int.natCast_dvd_natCast.mp h)), sub_zero]

end SpecS8

section SpecS10

def coreA (φ : ℕ → ℤ) (e : ℕ × ℕ) : ℤ :=
  if e.2 < e.1 ∧ e.1 - e.2 ∣ e.2 then φ (e.1 - e.2) else 0

def coreB (φ : ℕ → ℤ) (e : ℕ × ℕ) : ℤ :=
  if e.1 < e.2 ∧ e.2 - e.1 ∣ e.2 then φ (e.2 - e.1) else 0

theorem core_eq_coreA_add_coreB (φ : ℕ → ℤ) (e : ℕ × ℕ) :
    (if e.1 = e.2 then (0 : ℤ)
      else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then φ (e.1 - e.2) else 0)
      else (if e.2 - e.1 ∣ e.2 then φ (e.2 - e.1) else 0)) = coreA φ e + coreB φ e := by
  unfold coreA coreB
  rcases lt_trichotomy e.1 e.2 with h | h | h
  · have hA : ¬(e.2 < e.1 ∧ e.1 - e.2 ∣ e.2) := fun hc => (not_lt.mpr h.le) hc.1
    rw [if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg hA, zero_add]
    by_cases hd : e.2 - e.1 ∣ e.2
    · rw [if_pos hd, if_pos (show e.1 < e.2 ∧ e.2 - e.1 ∣ e.2 from ⟨h, hd⟩)]
    · rw [if_neg hd, if_neg (show ¬(e.1 < e.2 ∧ e.2 - e.1 ∣ e.2) from fun hc => hd hc.2)]
  · have hA : ¬(e.2 < e.1 ∧ e.1 - e.2 ∣ e.2) := fun hc => absurd hc.1 (by omega)
    have hB : ¬(e.1 < e.2 ∧ e.2 - e.1 ∣ e.2) := fun hc => absurd hc.1 (by omega)
    rw [if_pos h, if_neg hA, if_neg hB, add_zero]
  · have hB : ¬(e.1 < e.2 ∧ e.2 - e.1 ∣ e.2) := fun hc => (not_lt.mpr h.le) hc.1
    rw [if_neg h.ne', if_pos h, if_neg hB, add_zero]
    by_cases hd : e.1 - e.2 ∣ e.2
    · rw [if_pos hd, if_pos (show e.2 < e.1 ∧ e.1 - e.2 ∣ e.2 from ⟨h, hd⟩)]
    · rw [if_neg hd, if_neg (show ¬(e.2 < e.1 ∧ e.1 - e.2 ∣ e.2) from fun hc => hd hc.2)]

theorem lineA_factor (p k d q : ℕ) (hkp : k ≤ p) :
    k * (d * (q + 1)) + (p - k) * (d * q) = d * (k + p * q) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkp
  rw [Nat.add_sub_cancel_left]
  ring

theorem lineB_factor (p k d q : ℕ) (hkp : k ≤ p) :
    k * (d * q) + (p - k) * (d * (q + 1)) = d * (p * q + (p - k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkp
  rw [Nat.add_sub_cancel_left]
  ring

theorem mem_filterA {p k N : ℕ} (hk : 0 < k) (hkp : k < p) {e : ℕ × ℕ} :
    e ∈ (reidxLineSet k (p - k) N).filter (fun e => e.2 < e.1 ∧ e.1 - e.2 ∣ e.2) ↔
      ∃ d q, 0 < d ∧ e = (d * (q + 1), d * q) ∧ N = d * (k + p * q) := by
  rw [Finset.mem_filter, mem_reidxLineSet hk (Nat.sub_pos_of_lt hkp)]
  constructor
  · rintro ⟨hl, hlt, hdv⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hd, Nat.add_sub_cancel_left] at hdv
    obtain ⟨q, hq⟩ := hdv
    refine ⟨d, q, by omega, Prod.ext ?_ hq, ?_⟩
    · show e.1 = d * (q + 1)
      rw [mul_add_one, ← hq]
      exact hd
    · rw [← hl, ← lineA_factor p k d q hkp.le, mul_add_one, ← hq, ← hd]
  · rintro ⟨d, q, hd, rfl, rfl⟩
    refine ⟨lineA_factor p k d q hkp.le, ?_, ?_⟩
    · show d * q < d * (q + 1)
      rw [mul_add_one]
      omega
    · show d * (q + 1) - d * q ∣ d * q
      rw [mul_add_one, Nat.add_sub_cancel_left]
      exact dvd_mul_right d q

theorem mem_filterB {p k N : ℕ} (hk : 0 < k) (hkp : k < p) {e : ℕ × ℕ} :
    e ∈ (reidxLineSet k (p - k) N).filter (fun e => e.1 < e.2 ∧ e.2 - e.1 ∣ e.2) ↔
      ∃ d q, 0 < d ∧ e = (d * q, d * (q + 1)) ∧ N = d * (p * q + (p - k)) := by
  rw [Finset.mem_filter, mem_reidxLineSet hk (Nat.sub_pos_of_lt hkp)]
  constructor
  · rintro ⟨hl, hlt, hdv⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hd, Nat.add_sub_cancel_left] at hdv
    obtain ⟨q, hq⟩ := (Nat.dvd_add_right (dvd_refl d)).mp ((add_comm e.1 d) ▸ hdv)
    refine ⟨d, q, by omega, Prod.ext hq ?_, ?_⟩
    · show e.2 = d * (q + 1)
      rw [mul_add_one, ← hq]
      exact hd
    · rw [← hl, ← lineB_factor p k d q hkp.le, mul_add_one, ← hq, ← hd]
  · rintro ⟨d, q, hd, rfl, rfl⟩
    refine ⟨lineB_factor p k d q hkp.le, ?_, ?_⟩
    · show d * q < d * (q + 1)
      rw [mul_add_one]
      omega
    · show d * (q + 1) - d * q ∣ d * (q + 1)
      rw [mul_add_one, Nat.add_sub_cancel_left]
      exact (Nat.dvd_add_right (dvd_mul_right d q)).mpr (dvd_refl d)

theorem sum_line_coreA (φ : ℕ → ℤ) (p k N : ℕ) (hk : 0 < k) (hkp : k < p) :
    ∑ e ∈ reidxLineSet k (p - k) N, coreA φ e =
      ∑ d ∈ N.divisors, if N / d % p = k then φ d else 0 := by
  have hp0 : 0 < p := lt_trans hk hkp
  rw [show (∑ e ∈ reidxLineSet k (p - k) N, coreA φ e) =
      ∑ e ∈ (reidxLineSet k (p - k) N).filter (fun e => e.2 < e.1 ∧ e.1 - e.2 ∣ e.2),
        φ (e.1 - e.2) by rw [Finset.sum_filter]; rfl,
    ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun e => e.1 - e.2) (fun d => (d * (N / d / p + 1), d * (N / d / p)))
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨d, q, hd, rfl, hN⟩ := (mem_filterA hk hkp).mp he
    have hsub : d * (q + 1) - d * q = d := by rw [mul_add_one, Nat.add_sub_cancel_left]
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show d * (q + 1) - d * q ∣ N
      rw [hsub, hN]
      exact dvd_mul_right _ _
    · rw [hN]
      exact (Nat.mul_pos hd (Nat.add_pos_left hk _)).ne'
    · show N / (d * (q + 1) - d * q) % p = k
      rw [hsub, hN, Nat.mul_div_cancel_left _ hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkp]
  · intro d hd'
    rw [Finset.mem_filter, Nat.mem_divisors] at hd'
    obtain ⟨⟨hdN, hN0⟩, hr⟩ := hd'
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdN (Nat.pos_of_ne_zero hN0)
    refine (mem_filterA hk hkp).mpr ⟨d, N / d / p, hd, rfl, ?_⟩
    calc N = d * (N / d) := (Nat.mul_div_cancel' hdN).symm
      _ = d * (N / d % p + p * (N / d / p)) := by rw [Nat.mod_add_div]
      _ = d * (k + p * (N / d / p)) := by rw [hr]
  · intro e he
    obtain ⟨d, q, hd, rfl, hN⟩ := (mem_filterA hk hkp).mp he
    have hsub : d * (q + 1) - d * q = d := by rw [mul_add_one, Nat.add_sub_cancel_left]
    show ((d * (q + 1) - d * q) * (N / (d * (q + 1) - d * q) / p + 1),
        (d * (q + 1) - d * q) * (N / (d * (q + 1) - d * q) / p)) = (d * (q + 1), d * q)
    rw [hsub, hN, Nat.mul_div_cancel_left _ hd, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hkp,
      zero_add]
  · intro d hd'
    show d * (N / d / p + 1) - d * (N / d / p) = d
    rw [mul_add_one, Nat.add_sub_cancel_left]
  · intro e _
    rfl

theorem sum_line_coreB (φ : ℕ → ℤ) (p k N : ℕ) (hk : 0 < k) (hkp : k < p) :
    ∑ e ∈ reidxLineSet k (p - k) N, coreB φ e =
      ∑ d ∈ N.divisors, if N / d % p = p - k then φ d else 0 := by
  have hp0 : 0 < p := lt_trans hk hkp
  have hpk : p - k < p := Nat.sub_lt hp0 hk
  rw [show (∑ e ∈ reidxLineSet k (p - k) N, coreB φ e) =
      ∑ e ∈ (reidxLineSet k (p - k) N).filter (fun e => e.1 < e.2 ∧ e.2 - e.1 ∣ e.2),
        φ (e.2 - e.1) by rw [Finset.sum_filter]; rfl,
    ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun e => e.2 - e.1) (fun d => (d * (N / d / p), d * (N / d / p + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨d, q, hd, rfl, hN⟩ := (mem_filterB hk hkp).mp he
    have hsub : d * (q + 1) - d * q = d := by rw [mul_add_one, Nat.add_sub_cancel_left]
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show d * (q + 1) - d * q ∣ N
      rw [hsub, hN]
      exact dvd_mul_right _ _
    · rw [hN]
      exact (Nat.mul_pos hd (Nat.add_pos_right _ (Nat.sub_pos_of_lt hkp))).ne'
    · show N / (d * (q + 1) - d * q) % p = p - k
      rw [hsub, hN, Nat.mul_div_cancel_left _ hd, Nat.mul_add_mod, Nat.mod_eq_of_lt hpk]
  · intro d hd'
    rw [Finset.mem_filter, Nat.mem_divisors] at hd'
    obtain ⟨⟨hdN, hN0⟩, hr⟩ := hd'
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdN (Nat.pos_of_ne_zero hN0)
    refine (mem_filterB hk hkp).mpr ⟨d, N / d / p, hd, rfl, ?_⟩
    calc N = d * (N / d) := (Nat.mul_div_cancel' hdN).symm
      _ = d * (p * (N / d / p) + N / d % p) := by rw [Nat.div_add_mod]
      _ = d * (p * (N / d / p) + (p - k)) := by rw [hr]
  · intro e he
    obtain ⟨d, q, hd, rfl, hN⟩ := (mem_filterB hk hkp).mp he
    have hsub : d * (q + 1) - d * q = d := by rw [mul_add_one, Nat.add_sub_cancel_left]
    show ((d * (q + 1) - d * q) * (N / (d * (q + 1) - d * q) / p),
        (d * (q + 1) - d * q) * (N / (d * (q + 1) - d * q) / p + 1)) = (d * q, d * (q + 1))
    rw [hsub, hN, Nat.mul_div_cancel_left _ hd, Nat.mul_add_div hp0, Nat.div_eq_of_lt hpk, add_zero]
  · intro d hd'
    show d * (N / d / p + 1) - d * (N / d / p) = d
    rw [mul_add_one, Nat.add_sub_cancel_left]
  · intro e _
    rfl

theorem sum_Icc_indicator_pm (h M : ℕ) (x : ℤ) :
    ∑ k ∈ Finset.Icc 1 h, ((if M % (2 * h + 1) = k then x else 0) +
      (if M % (2 * h + 1) = 2 * h + 1 - k then x else 0)) = if ¬(2 * h + 1 ∣ M) then x else 0 := by
  have hr : M % (2 * h + 1) < 2 * h + 1 := Nat.mod_lt _ (by omega)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  have h2 : ∑ k ∈ Finset.Icc 1 h, (if M % (2 * h + 1) = 2 * h + 1 - k then x else 0) =
      if h + 1 ≤ M % (2 * h + 1) then x else 0 := by
    by_cases hr1 : h + 1 ≤ M % (2 * h + 1)
    · rw [if_pos hr1, Finset.sum_eq_single_of_mem (2 * h + 1 - M % (2 * h + 1))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
      · rw [if_pos (show M % (2 * h + 1) = 2 * h + 1 - (2 * h + 1 - M % (2 * h + 1)) by omega)]
      · intro k hk hne
        rw [Finset.mem_Icc] at hk
        rw [if_neg (show ¬(M % (2 * h + 1) = 2 * h + 1 - k) by omega)]
    · rw [if_neg hr1]
      exact Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Icc] at hk
        rw [if_neg (show ¬(M % (2 * h + 1) = 2 * h + 1 - k) by omega)]
  rw [h2]
  by_cases hdvd : 2 * h + 1 ∣ M
  · have h0 : M % (2 * h + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvd
    rw [if_neg (show ¬¬(2 * h + 1 ∣ M) from fun hc => hc hdvd),
      if_neg (show ¬(M % (2 * h + 1) ∈ Finset.Icc 1 h) by rw [Finset.mem_Icc]; omega),
      if_neg (show ¬(h + 1 ≤ M % (2 * h + 1)) by omega), add_zero]
  · have h0 : M % (2 * h + 1) ≠ 0 := fun hc => hdvd (Nat.dvd_of_mod_eq_zero hc)
    rw [if_pos hdvd]
    by_cases hle : M % (2 * h + 1) ≤ h
    · rw [if_pos (show M % (2 * h + 1) ∈ Finset.Icc 1 h by rw [Finset.mem_Icc]; omega),
        if_neg (show ¬(h + 1 ≤ M % (2 * h + 1)) by omega), add_zero]
    · rw [if_neg (show ¬(M % (2 * h + 1) ∈ Finset.Icc 1 h) by rw [Finset.mem_Icc]; omega),
        if_pos (show h + 1 ≤ M % (2 * h + 1) by omega), zero_add]

theorem reidx_core_roadB (p : ℕ) (hp : Odd p) (φ : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 (p / 2), ∑ e ∈ reidxLineSet k (p - k) N,
        (if e.1 = e.2 then (0 : ℤ)
         else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then φ (e.1 - e.2) else 0)
         else (if e.2 - e.1 ∣ e.2 then φ (e.2 - e.1) else 0)) =
      ∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), φ d := by
  obtain ⟨h, rfl⟩ := hp
  have hh : (2 * h + 1) / 2 = h := by omega
  rw [hh]
  have inner : ∀ k ∈ Finset.Icc 1 h, ∑ e ∈ reidxLineSet k (2 * h + 1 - k) N,
      (if e.1 = e.2 then (0 : ℤ)
       else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then φ (e.1 - e.2) else 0)
       else (if e.2 - e.1 ∣ e.2 then φ (e.2 - e.1) else 0)) =
      ∑ d ∈ N.divisors, ((if N / d % (2 * h + 1) = k then φ d else 0) +
        (if N / d % (2 * h + 1) = 2 * h + 1 - k then φ d else 0)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.sum_congr rfl fun e _ => core_eq_coreA_add_coreB φ e, Finset.sum_add_distrib,
      sum_line_coreA φ _ k N hk.1 (by omega), sum_line_coreB φ _ k N hk.1 (by omega),
      ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl inner, Finset.sum_comm, Finset.sum_filter]
  exact Finset.sum_congr rfl fun d _ => sum_Icc_indicator_pm h (N / d) (φ d)

end SpecS10

section SpecS11

theorem sum_divisors_filter_dvd (p : ℕ) (hp : 0 < p) (φ : ℕ → ℤ) (N : ℕ) :
    ∑ d ∈ N.divisors.filter (fun d => p ∣ N / d), φ d =
      if p ∣ N then ∑ d ∈ (N / p).divisors, φ d else 0 := by
  by_cases hpN : p ∣ N
  · rw [if_pos hpN]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdN, hN0⟩, hpd⟩
      refine ⟨(Nat.dvd_div_iff_mul_dvd hpN).mpr ?_, ?_⟩
      · rw [mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hdN).mp hpd
      · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hpN) hp).ne'
    · rintro ⟨hdq, hq0⟩
      have hN0 : N ≠ 0 := fun h => hq0 (by rw [h, Nat.zero_div])
      have hpd : p * d ∣ N := (Nat.dvd_div_iff_mul_dvd hpN).mp hdq
      have hdN : d ∣ N := dvd_trans (dvd_mul_left d p) hpd
      refine ⟨⟨hdN, hN0⟩, (Nat.dvd_div_iff_mul_dvd hdN).mpr ?_⟩
      rw [mul_comm]
      exact hpd
  · rw [if_neg hpN]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (dvd_trans hd.2 (Nat.div_dvd_of_dvd hd.1.1)) hpN

theorem reidx_divisor_split_roadB (p : ℕ) (hp : 0 < p) (φ : ℕ → ℤ) (N : ℕ) :
    ∑ d ∈ N.divisors.filter (fun d => ¬ p ∣ N / d), φ d =
      (∑ d ∈ N.divisors, φ d) - (if p ∣ N then ∑ d ∈ (N / p).divisors, φ d else 0) := by
  rw [← sum_divisors_filter_dvd p hp φ N, eq_sub_iff_add_eq, add_comm,
    Finset.sum_filter_add_sum_filter_not]

theorem sum_slotSubst_tateUnivEven (K : Type*) [CommRing K] (φ : ℕ → ℤ) (p : ℕ) [NeZero p]
    (hp : Odd p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ) :
    ∑ k ∈ Finset.Icc 1 (p / 2),
        HahnSeries.ofPowerSeries ℤ K (slotSubst K p (ζ ^ (b * k)) k (tateUnivEven φ)) =
      qTwist (ζ ^ b) (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)) -
        qExpand K p (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, φ d)) :=
  sum_slotSubst_tateUnivEven_of_core K φ p ζ hζ b (fun N => reidx_core_roadB p hp φ N)
    fun N => reidx_divisor_split_roadB p (NeZero.pos p) φ N

end SpecS11

section ReidxOneLiners

theorem tateA4_eq :
    tateA4 = (-5 : ℤ) • PowerSeries.mk fun N => ∑ d ∈ N.divisors, (d : ℤ) ^ 3 := by
  ext n
  rw [coeff_tateA4, map_zsmul, PowerSeries.coeff_mk]
  show _ = (-5 : ℤ) • (∑ d ∈ n.divisors, (d : ℤ) ^ 3)
  simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat, neg_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib]

theorem tateA6_eq (h : ∀ d, tateB d = (d : ℤ) ^ 3 + 7 * tateC d) :
    tateA6 = -(PowerSeries.mk fun N => ∑ d ∈ N.divisors, (d : ℤ) ^ 3)
              - (7 : ℤ) • PowerSeries.mk fun N => ∑ d ∈ N.divisors, tateC d := by
  ext n
  rw [coeff_tateA6, map_sub, map_neg, map_zsmul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  show _ = -(∑ d ∈ n.divisors, (d : ℤ) ^ 3) - (7 : ℤ) • (∑ d ∈ n.divisors, tateC d)
  simp only [zsmul_eq_mul, Int.cast_ofNat, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by rw [h d]; ring

end ReidxOneLiners

private theorem veluQuotient_nonToricSlotSet (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (hp : Odd p)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    (tateBase K p).veluQuotient (nonToricSlotSet K p ζ b) =
      (tateLaurent K).map (qTwist (ζ ^ b)) := by
  have hT := veluT_tateUniv hE
  have hW := veluW_tateUniv hE
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hkp : ∀ k ∈ Finset.Icc 1 (p / 2), 0 < k ∧ k < p := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  have hTSum : (tateBase K p).veluTSum (nonToricSlotSet K p ζ b) =
      qTwist (ζ ^ b) (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, (d : ℤ) ^ 3)) -
        qExpand K p (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, (d : ℤ) ^ 3)) := by
    have h1 : (tateBase K p).veluTSum (nonToricSlotSet K p ζ b) =
        ∑ k ∈ Finset.Icc 1 (p / 2),
          (tateBase K p).veluT (nonToricPoint K p (ζ ^ (b * k)) k).1
            (nonToricPoint K p (ζ ^ (b * k)) k).2 :=
      sum_nonToricSlotSet K p ζ b fun P => (tateBase K p).veluT P.1 P.2
    have h2 : ∑ k ∈ Finset.Icc 1 (p / 2),
        (tateBase K p).veluT (nonToricPoint K p (ζ ^ (b * k)) k).1
          (nonToricPoint K p (ζ ^ (b * k)) k).2 =
        ∑ k ∈ Finset.Icc 1 (p / 2),
          HahnSeries.ofPowerSeries ℤ K (slotSubst K p (ζ ^ (b * k)) k tateUnivT) :=
      Finset.sum_congr rfl fun k hk =>
        veluT_nonToricPoint K p (ζ ^ (b * k)) k (hkp k hk).1 (hkp k hk).2 hT
    rw [h1, h2]
    exact sum_slotSubst_tateUnivEven K (fun n => (n : ℤ) ^ 3) p hp ζ hζ b
  have hWSum : (tateBase K p).veluWSum (nonToricSlotSet K p ζ b) =
      qTwist (ζ ^ b) (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, tateC d)) -
        qExpand K p (laurentOfInt K (PowerSeries.mk fun N => ∑ d ∈ N.divisors, tateC d)) := by
    have h1 : (tateBase K p).veluWSum (nonToricSlotSet K p ζ b) =
        ∑ k ∈ Finset.Icc 1 (p / 2),
          (tateBase K p).veluW (nonToricPoint K p (ζ ^ (b * k)) k).1
            (nonToricPoint K p (ζ ^ (b * k)) k).2 :=
      sum_nonToricSlotSet K p ζ b fun P => (tateBase K p).veluW P.1 P.2
    have h2 : ∑ k ∈ Finset.Icc 1 (p / 2),
        (tateBase K p).veluW (nonToricPoint K p (ζ ^ (b * k)) k).1
          (nonToricPoint K p (ζ ^ (b * k)) k).2 =
        ∑ k ∈ Finset.Icc 1 (p / 2),
          HahnSeries.ofPowerSeries ℤ K (slotSubst K p (ζ ^ (b * k)) k tateUnivW) :=
      Finset.sum_congr rfl fun k hk =>
        veluW_nonToricPoint K p (ζ ^ (b * k)) k (hkp k hk).1 (hkp k hk).2 hW
    rw [h1, h2]
    exact sum_slotSubst_tateUnivEven K tateC p hp ζ hζ b
  have ha₁ : (tateBase K p).a₁ = 1 := by
    show qExpand K p (laurentOfInt K tatePowerSeries.a₁) = 1
    rw [tatePowerSeries_a₁, map_one, map_one]
  have ha₁' : ((tateLaurent K).map (qTwist (ζ ^ b))).a₁ = 1 := by
    show qTwist (ζ ^ b) (laurentOfInt K tatePowerSeries.a₁) = 1
    rw [tatePowerSeries_a₁, map_one, map_one]
  have ha₂ : (tateBase K p).a₂ = 0 := by
    show qExpand K p (laurentOfInt K tatePowerSeries.a₂) = 0
    rw [tatePowerSeries_a₂, map_zero, map_zero]
  have ha₂' : ((tateLaurent K).map (qTwist (ζ ^ b))).a₂ = 0 := by
    show qTwist (ζ ^ b) (laurentOfInt K tatePowerSeries.a₂) = 0
    rw [tatePowerSeries_a₂, map_zero, map_zero]
  have ha₃ : (tateBase K p).a₃ = 0 := by
    show qExpand K p (laurentOfInt K tatePowerSeries.a₃) = 0
    rw [tatePowerSeries_a₃, map_zero, map_zero]
  have ha₃' : ((tateLaurent K).map (qTwist (ζ ^ b))).a₃ = 0 := by
    show qTwist (ζ ^ b) (laurentOfInt K tatePowerSeries.a₃) = 0
    rw [tatePowerSeries_a₃, map_zero, map_zero]
  have hb₂ : (tateBase K p).b₂ = 1 := by
    simp [WeierstrassCurve.b₂, ha₁, ha₂]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · rw [WeierstrassCurve.veluQuotient_a₁, ha₁, ha₁']
  · rw [WeierstrassCurve.veluQuotient_a₂, ha₂, ha₂']
  · rw [WeierstrassCurve.veluQuotient_a₃, ha₃, ha₃']
  · rw [WeierstrassCurve.veluQuotient_a₄, hTSum,
      show (tateBase K p).a₄ = qExpand K p (laurentOfInt K tateA4) from rfl,
      show ((tateLaurent K).map (qTwist (ζ ^ b))).a₄ =
        qTwist (ζ ^ b) (laurentOfInt K tateA4) from rfl, tateA4_eq]
    simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_ofNat]
    ring
  · rw [WeierstrassCurve.veluQuotient_a₆, hTSum, hWSum, hb₂,
      show (tateBase K p).a₆ = qExpand K p (laurentOfInt K tateA6) from rfl,
      show ((tateLaurent K).map (qTwist (ζ ^ b))).a₆ =
        qTwist (ζ ^ b) (laurentOfInt K tateA6) from rfl,
      tateA6_eq tateB_eq_pow_add_tateC]
    simp only [zsmul_eq_mul, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat]
    ring

private theorem isElliptic_veluQuotient_nonToricSlotSet (K : Type*) [CommRing K] (p : ℕ) [NeZero p]
    (hp : Odd p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    ((tateBase K p).veluQuotient (nonToricSlotSet K p ζ b)).IsElliptic := by
  rw [veluQuotient_nonToricSlotSet K p hp ζ hζ b hE]
  infer_instance

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet.ModularCurve"

#check @ModularCurve.veluQuotient_nonToricSlotSet
#check @ModularCurve.sum_slotSubst_tateUnivEven
#check @ModularCurve.veluT_tateUniv
#check @ModularCurve.veluW_tateUniv
example : NoZeroDivisors (MvPowerSeries (Fin 2) ℤ) := inferInstance

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet.ModularCurve in

theorem solution (K : Type*) [CommRing K] (p : ℕ) [NeZero p]
    (hp : Odd p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    (tateBase K p).veluQuotient (nonToricSlotSet K p ζ b) =
      (tateLaurent K).map (qTwist (ζ ^ b)) :=
  ModularCurve.veluQuotient_nonToricSlotSet K p hp ζ hζ b hE

#print axioms solution

end S_ModularCurve_veluQuotient_nonToricSlotSet
end P2MW
export P2MW.S_ModularCurve_veluQuotient_nonToricSlotSet (solution)
