-- Prove2me | solution 1 for ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/615b1a63-ea38-5d09-9e08-241809f5c2fe

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
import Theorems.Thm_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open scoped MatrixGroups

namespace P2mSolDvdQCoeffZeroSel

open Nat

def A (p r : ℕ) : ℤ := (p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)

theorem A_eq (p r : ℕ) (hr : 1 ≤ r) :
    A p r = ((p + 1).choose r : ℤ) - (p + 1 : ℤ) * (p.choose (r - 1) : ℤ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [A, Nat.add_sub_cancel, Nat.choose_succ_succ', Nat.cast_add]
  ring

theorem choose_pow_mul_modEq (ℓ : ℕ) [Fact ℓ.Prime] (v m : ℕ) :
    ((ℓ ^ v * m).choose (ℓ ^ v) : ℤ) ≡ m [ZMOD ℓ] := by
  have := Choose.choose_pow_mul_pow_mul_modEq_choose (p := ℓ) (k := v) (a := m) (b := 1)
  simpa using this

theorem choose_mul_add_one_modEq (ℓ : ℕ) [Fact ℓ.Prime] (N K e : ℕ) (he : e < ℓ) :
    ((ℓ * N + 1).choose (ℓ * K + e) : ℤ) ≡ (Nat.choose 1 e : ℕ) * (N.choose K : ℕ) [ZMOD ℓ] := by
  have hℓ : ℓ.Prime := Fact.out
  have h2 : 2 ≤ ℓ := hℓ.two_le
  have step := Choose.choose_modEq_choose_mod_mul_choose_div (n := ℓ * N + 1) (k := ℓ * K + e)
    (p := ℓ)
  have hn : (ℓ * N + 1) % ℓ = 1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  have hn' : (ℓ * N + 1) / ℓ = N := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
  have hk : (ℓ * K + e) % ℓ = e := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt he
  have hk' : (ℓ * K + e) / ℓ = K := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt he, add_zero]
  rw [hn, hn', hk, hk'] at step
  exact_mod_cast step

theorem choose_pow_mul_add_one_modEq (ℓ : ℕ) [Fact ℓ.Prime] (v m : ℕ) (hv : 1 ≤ v) :
    ((ℓ ^ v * m + 1).choose (ℓ ^ v) : ℤ) ≡ m [ZMOD ℓ] := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have e1 : ℓ ^ (w + 1) * m + 1 = ℓ * (ℓ ^ w * m) + 1 := by ring
  have e2 : ℓ ^ (w + 1) = ℓ * ℓ ^ w + 0 := by ring
  have step := choose_mul_add_one_modEq ℓ (ℓ ^ w * m) (ℓ ^ w) 0 hℓ.pos
  rw [← e1, ← e2] at step
  refine step.trans ?_
  simpa using choose_pow_mul_modEq ℓ w m

theorem choose_pow_mul_add_one_sub_one_modEq (ℓ : ℕ) [Fact ℓ.Prime] (h3 : 3 ≤ ℓ) (v m : ℕ)
    (hv : 1 ≤ v) : ((ℓ ^ v * m + 1).choose (ℓ ^ v - 1) : ℤ) ≡ 0 [ZMOD ℓ] := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hpos : 1 ≤ ℓ ^ w := Nat.one_le_pow _ _ (by omega)
  obtain ⟨Y, hY⟩ : ∃ Y, ℓ ^ w = Y + 1 := ⟨ℓ ^ w - 1, by omega⟩
  have e1 : ℓ ^ (w + 1) * m + 1 = ℓ * (ℓ ^ w * m) + 1 := by ring
  have e2 : ℓ ^ (w + 1) - 1 = ℓ * Y + (ℓ - 1) := by
    rw [pow_succ', hY, mul_add, mul_one]
    generalize ℓ * Y = Z
    omega
  have step := choose_mul_add_one_modEq ℓ (ℓ ^ w * m) Y (ℓ - 1) (by omega)
  rw [← e1, ← e2, Nat.choose_eq_zero_of_lt (show 1 < ℓ - 1 by omega)] at step
  simpa using step

theorem two_mul_choose_two (p : ℕ) :
    (2 : ℤ) * ((p.choose 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
  rcases p with _ | q
  · norm_num [Nat.choose_eq_zero_of_lt]
  have a := Nat.add_one_mul_choose_eq q 1
  norm_num [Nat.choose_one_right] at a

  have a' : ((q + 1 : ℕ) : ℤ) * (q : ℤ) = (((q + 1).choose 2 : ℕ) : ℤ) * 2 := by exact_mod_cast a
  push_cast at a' ⊢
  linear_combination -a'

theorem six_mul_choose_three (p : ℕ) :
    (6 : ℤ) * ((p.choose 3 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 1) * ((p : ℤ) - 2) := by
  rcases p with _ | q
  · norm_num [Nat.choose_eq_zero_of_lt]
  have a := Nat.add_one_mul_choose_eq q 2
  norm_num at a

  have a' : ((q + 1 : ℕ) : ℤ) * ((q.choose 2 : ℕ) : ℤ) = (((q + 1).choose 3 : ℕ) : ℤ) * 3 := by
    exact_mod_cast a
  have b := two_mul_choose_two q
  push_cast at a' ⊢
  linear_combination (-2 : ℤ) * a' + ((q : ℤ) + 1) * b

theorem exists_good (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hℓp : ℓ ≠ p) :
    ∃ r : ℕ, 1 ≤ r ∧ ¬ ((ℓ - 1 : ℕ) : ℤ) ∣ 2 * (r : ℤ) ∧ ¬ (ℓ : ℤ) ∣ A p r := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓint : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hℓp' : ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)

  have absorb : ∀ (X : ℤ) (m : ℕ), X ≡ m [ZMOD ℓ] → (ℓ : ℤ) ∣ X → ℓ ∣ m := by
    intro X m hX hd
    have h1 : (ℓ : ℤ) ∣ (m : ℤ) - X := Int.ModEq.dvd hX
    have h2 : (ℓ : ℤ) ∣ (m : ℤ) := by simpa using dvd_add h1 hd
    exact_mod_cast h2
  by_cases hplus : ℓ ∣ p + 1
  ·
    set v := padicValNat ℓ (p + 1) with hv
    obtain ⟨m, hm⟩ : ℓ ^ v ∣ p + 1 := pow_padicValNat_dvd
    have hv1 : 1 ≤ v := one_le_padicValNat_of_dvd (by omega) hplus
    have hℓm : ¬ ℓ ∣ m := by
      intro hd
      have : ℓ ^ (v + 1) ∣ p + 1 := by
        rw [hm, pow_succ]; exact Nat.mul_dvd_mul_left _ hd
      exact pow_succ_padicValNat_not_dvd (p := ℓ) (n := p + 1) (by omega) this
    refine ⟨ℓ ^ v, Nat.one_le_pow _ _ hℓ.pos, ?_, ?_⟩
    · intro hd
      have hd' : (ℓ - 1) ∣ 2 * ℓ ^ v := by exact_mod_cast hd
      have hcop : Nat.Coprime (ℓ - 1) (ℓ ^ v) := by
        apply Nat.Coprime.pow_right
        have := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (ℓ - 1))
        rwa [Nat.sub_add_cancel hℓ.one_le] at this
      have := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hd')
      omega
    · rw [A_eq _ _ (Nat.one_le_pow _ _ hℓ.pos)]
      intro hd
      have h1 : (ℓ : ℤ) ∣ (p + 1 : ℤ) * (p.choose (ℓ ^ v - 1) : ℤ) :=
        Dvd.dvd.mul_right (by exact_mod_cast hplus) _
      have h2 : (ℓ : ℤ) ∣ ((p + 1).choose (ℓ ^ v) : ℤ) := by simpa using dvd_add hd h1
      rw [hm] at h2
      exact hℓm (absorb _ _ (choose_pow_mul_modEq ℓ v m) h2)
  · by_cases hfive : ℓ = 5 ∧ ℓ ∣ p - 1
    ·
      obtain ⟨rfl, hminus⟩ := hfive
      have hp2 : 2 ≤ p := hp.two_le
      set v := padicValNat 5 (p - 1) with hv
      obtain ⟨m, hm⟩ : 5 ^ v ∣ p - 1 := pow_padicValNat_dvd
      have hv1 : 1 ≤ v := one_le_padicValNat_of_dvd (by omega) hminus
      have h5m : ¬ 5 ∣ m := by
        intro hd
        have : 5 ^ (v + 1) ∣ p - 1 := by
          rw [hm, pow_succ]; exact Nat.mul_dvd_mul_left _ hd
        exact pow_succ_padicValNat_not_dvd (p := 5) (n := p - 1) (by omega) this
      have hp' : p = 5 ^ v * m + 1 := by omega
      refine ⟨5 ^ v, Nat.one_le_pow _ _ (by norm_num), ?_, ?_⟩
      · intro hd
        have hd' : (4 : ℤ) ∣ 2 * 5 ^ v := by
          have e : ((5 - 1 : ℕ) : ℤ) = 4 := by norm_num
          rw [e] at hd
          exact_mod_cast hd
        have h1 : (2 : ℤ) * 5 ^ v ≡ 2 * 1 ^ v [ZMOD 4] :=
          Int.ModEq.mul_left 2 (Int.ModEq.pow v (show (5 : ℤ) ≡ 1 [ZMOD 4] by decide))
        have h2 := ((Int.modEq_zero_iff_dvd.mpr hd').symm.trans h1)
        rw [one_pow, mul_one] at h2
        exact absurd h2 (by decide)
      · intro hd
        simp only [A] at hd
        rw [hp'] at hd
        have e1 := choose_pow_mul_add_one_modEq 5 v m hv1
        have e2 := choose_pow_mul_add_one_sub_one_modEq 5 (by norm_num) v m hv1
        have e3 := Int.ModEq.sub e1 (Int.ModEq.mul_left (((5 ^ v * m + 1 : ℕ) : ℤ)) e2)
        rw [mul_zero, sub_zero] at e3
        exact h5m (absorb _ _ e3 hd)
    ·
      by_cases hℓ5 : ℓ = 5
      ·
        subst hℓ5
        have hminus : ¬ 5 ∣ p - 1 := fun h => hfive ⟨rfl, h⟩
        refine ⟨3, by norm_num, by norm_num, ?_⟩
        intro hd
        simp only [A, show (3 : ℕ) - 1 = 2 from rfl] at hd
        have s := six_mul_choose_three p
        have b := two_mul_choose_two p

        have key : (6 : ℤ) * (((p.choose 3 : ℕ) : ℤ) - (p : ℤ) * ((p.choose 2 : ℕ) : ℤ)) =
            -2 * ((p : ℤ) * ((p : ℤ) - 1) * ((p : ℤ) + 1)) := by
          linear_combination s + (-3 * (p : ℤ)) * b
        have hd6 : ((5 : ℕ) : ℤ) ∣ -2 * ((p : ℤ) * ((p : ℤ) - 1) * ((p : ℤ) + 1)) := by
          rw [← key]; exact Dvd.dvd.mul_left hd _
        have h5int : Prime ((5 : ℕ) : ℤ) := hℓint
        rcases h5int.dvd_or_dvd hd6 with h6 | h6
        · norm_num at h6
        rcases h5int.dvd_or_dvd h6 with h6 | h6
        · rcases h5int.dvd_or_dvd h6 with h7 | h7
          · exact hℓp' h7
          · refine hminus (Int.natCast_dvd_natCast.mp ?_)
            rw [Nat.cast_pred hp.pos]
            exact h7
        · exact hplus (Int.natCast_dvd_natCast.mp (by exact_mod_cast h6))
      ·
        have h7 : 7 ≤ ℓ := by
          rcases (show ℓ = 5 ∨ ℓ = 6 ∨ 7 ≤ ℓ by omega) with h | h | h
          · exact absurd h hℓ5
          · exact absurd (h ▸ hℓ) (by decide)
          · exact h
        refine ⟨2, by norm_num, ?_, ?_⟩
        · intro hd
          have hd' : (ℓ - 1) ∣ 4 := by exact_mod_cast hd
          have := Nat.le_of_dvd (by norm_num) hd'
          omega
        · intro hd
          simp only [A, show (2 : ℕ) - 1 = 1 from rfl, Nat.choose_one_right] at hd
          have b := two_mul_choose_two p

          have key : (2 : ℤ) * (((p.choose 2 : ℕ) : ℤ) - (p : ℤ) * (p : ℤ)) =
              -((p : ℤ) * ((p : ℤ) + 1)) := by
            linear_combination b
          have hd2 : (ℓ : ℤ) ∣ -((p : ℤ) * ((p : ℤ) + 1)) := by
            rw [← key]; exact Dvd.dvd.mul_left hd _
          rw [dvd_neg] at hd2
          rcases hℓint.dvd_or_dvd hd2 with h6 | h6
          · exact hℓp' h6
          · exact hplus (Int.natCast_dvd_natCast.mp (by exact_mod_cast h6))

end P2mSolDvdQCoeffZeroSel

open P2mSolDvdQCoeffZeroSel in
theorem solution (p ℓ : ℕ) [Fact p.Prime]
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hℓp : ℓ ≠ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (b : ℕ → ℤ) (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (ℓ : ℤ) ∣ b n) : (ℓ : ℤ) ∣ b 0 := by
  by_contra h0
  have hℓint : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ

  set B : PowerSeries ℤ := PowerSeries.mk b with hBdef
  have hB : B.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h := by
    ext n
    rw [PowerSeries.coeff_map, hBdef, PowerSeries.coeff_mk, eq_intCast, hb n]
    rfl
  have hB0 : PowerSeries.constantCoeff B = b 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hBdef, PowerSeries.coeff_mk]

  obtain ⟨r, hr1, hndvd, hA⟩ := exists_good p ℓ Fact.out hℓ h5 hℓp

  obtain ⟨F, T, hT, hTn, hT0⟩ :=
    ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two p h hB ℓ
      (fun n hn => by rw [hBdef, PowerSeries.coeff_mk]; exact hdvd n (by omega)) hr1
  have hT0' : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T := by
    intro hd
    have h1 : (ℓ : ℤ) ∣ (-PowerSeries.constantCoeff B) ^ r *
        ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by
      simpa using dvd_sub hd hT0
    rcases hℓint.dvd_or_dvd h1 with h2 | h2
    · have h3 := hℓint.dvd_of_dvd_pow h2
      rw [dvd_neg, hB0] at h3
      exact h0 h3
    · exact hA h2

  exact hndvd
    (ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne hℓ h5 F hT hTn hT0')

end S_ModularForm_dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff
end P2MW
export P2MW.S_ModularForm_dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff (solution)
