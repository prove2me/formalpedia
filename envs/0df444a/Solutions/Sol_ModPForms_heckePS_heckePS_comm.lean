-- Prove2me | solution 1 for ModPForms.heckePS_heckePS_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0f5e8363-347c-5e51-990e-304315777243

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_heckePS_heckePS_comm

set_option autoImplicit false

open ModPForms

namespace S2A

open PowerSeries

variable {F : Type} [Field F]

theorem coeff_heckePS (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) (n : ℕ) :
    coeff n (heckePS k ℓ φ) =
      coeff (n * ℓ) φ + if ℓ ∣ n then (ℓ : F) ^ (k - 1) * coeff (n / ℓ) φ else 0 := by
  unfold heckePS; rw [coeff_mk]

theorem heckePS_comm (k : ℤ) {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (hcop : Nat.Coprime ℓ ℓ')
    (φ : PowerSeries F) : heckePS k ℓ (heckePS k ℓ' φ) = heckePS k ℓ' (heckePS k ℓ φ) := by
  ext n
  simp only [coeff_heckePS]

  have h1 : ℓ' ∣ n * ℓ ↔ ℓ' ∣ n := hcop.symm.dvd_mul_right
  have h2 : ℓ ∣ n * ℓ' ↔ ℓ ∣ n := hcop.dvd_mul_right
  have e1 : n * ℓ * ℓ' = n * ℓ' * ℓ := by ring
  by_cases hn' : ℓ' ∣ n <;> by_cases hn : ℓ ∣ n
  ·
    obtain ⟨a, rfl⟩ := hn
    have hn'' : ℓ' ∣ a := (hcop.symm.dvd_mul_left).1 (by simpa [mul_comm] using hn')
    obtain ⟨b, rfl⟩ := hn''
    have d1 : ℓ * (ℓ' * b) * ℓ / ℓ' = ℓ * b * ℓ := by
      rw [show ℓ * (ℓ' * b) * ℓ = (ℓ * b * ℓ) * ℓ' by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ')]
    have d2 : ℓ * (ℓ' * b) / ℓ = ℓ' * b := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)
    have d3 : ℓ' * b / ℓ' = b := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ')
    have d4 : ℓ * (ℓ' * b) * ℓ' / ℓ = ℓ' * b * ℓ' := by
      rw [show ℓ * (ℓ' * b) * ℓ' = (ℓ' * b * ℓ') * ℓ by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ)]
    have d5 : ℓ * (ℓ' * b) / ℓ' = ℓ * b := by
      rw [show ℓ * (ℓ' * b) = (ℓ * b) * ℓ' by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ')]
    have d6 : ℓ * b / ℓ = b := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)
    have s1 : ℓ' ∣ ℓ * (ℓ' * b) * ℓ := ⟨ℓ * b * ℓ, by ring⟩
    have s2 : ℓ ∣ ℓ * (ℓ' * b) := ⟨ℓ' * b, rfl⟩
    have s3 : ℓ' ∣ ℓ' * b := ⟨b, rfl⟩
    have s4 : ℓ ∣ ℓ * (ℓ' * b) * ℓ' := ⟨ℓ' * b * ℓ', by ring⟩
    have s5 : ℓ' ∣ ℓ * (ℓ' * b) := ⟨ℓ * b, by ring⟩
    have s6 : ℓ ∣ ℓ * b := ⟨b, rfl⟩
    simp only [s1, s2, s3, s4, s5, s6, if_true, d1, d2, d3, d4, d5, d6, e1]
    ring
  ·
    have t1 : ¬ ℓ ∣ n * ℓ' := fun h => hn (h2.1 h)
    have t2 : ℓ' ∣ n * ℓ := h1.2 hn'
    have t3 : ¬ ℓ ∣ n / ℓ' := fun h => hn (by
      obtain ⟨c, hc⟩ := hn'
      rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ')] at h
      rw [hc]; exact Dvd.dvd.mul_left h _)
    have d1 : n * ℓ / ℓ' = n / ℓ' * ℓ := by
      obtain ⟨c, rfl⟩ := hn'
      rw [show ℓ' * c * ℓ = (c * ℓ) * ℓ' by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ'),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ')]
    simp only [hn', hn, t1, t2, t3, if_true, if_false, d1, e1]
    ring
  ·
    have t1 : ¬ ℓ' ∣ n * ℓ := fun h => hn' (h1.1 h)
    have t2 : ℓ ∣ n * ℓ' := h2.2 hn
    have t3 : ¬ ℓ' ∣ n / ℓ := fun h => hn' (by
      obtain ⟨c, hc⟩ := hn
      rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)] at h
      rw [hc]; exact Dvd.dvd.mul_left h _)
    have d1 : n * ℓ' / ℓ = n / ℓ * ℓ' := by
      obtain ⟨c, rfl⟩ := hn
      rw [show ℓ * c * ℓ' = (c * ℓ') * ℓ by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
    simp only [hn', hn, t1, t2, t3, if_true, if_false, d1, e1]
    ring
  ·
    have t1 : ¬ ℓ' ∣ n * ℓ := fun h => hn' (h1.1 h)
    have t2 : ¬ ℓ ∣ n * ℓ' := fun h => hn (h2.1 h)
    simp only [hn', hn, t1, t2, if_false, e1]

end S2A

open ModPForms

theorem solution
    (F : Type) [Field F] (k : ℤ) (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (ModPForms.heckePS k ℓ' φ) = ModPForms.heckePS k ℓ' (ModPForms.heckePS k ℓ φ) := by
  by_cases h : ℓ = ℓ'
  · subst h; rfl
  · exact S2A.heckePS_comm k hℓ.ne_zero hℓ'.ne_zero ((Nat.coprime_primes hℓ hℓ').2 h) φ

end S_ModPForms_heckePS_heckePS_comm
end P2MW
export P2MW.S_ModPForms_heckePS_heckePS_comm (solution)
