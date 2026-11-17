-- Prove2me | solution 1 for KnodelPrimeCordial.offset_zero_boundary__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:38:06.890386+00:00
-- url     : https://prove2.me/submissions/55bdc4df-5d0e-4f1a-aa29-f7ae5a38d9d4

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF
theorem KnodelPrimeCordial.offset_zero_boundary__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
    (n : ℕ) (hmod : n % 12 = 6) :
    ¬ Nat.Coprime (KnodelPrimeCordial.labelF 0)
      (KnodelPrimeCordial.labelF (n - 1)) := by
  have h0 : KnodelPrimeCordial.labelF 0 = 2 := by decide
  have hm : (n - 1) % 12 = 5 := by omega
  have h1 : KnodelPrimeCordial.labelF (n - 1) = n := by
    unfold KnodelPrimeCordial.labelF
    rw [hm]
    show n - 1 + 1 = n
    omega
  rw [h0, h1, Nat.coprime_two_left, Nat.not_odd_iff_even]
  exact ⟨n / 2, by omega⟩

theorem solution
    (n : ℕ) (hmod : n % 12 = 6) :
    ¬ Nat.Coprime (KnodelPrimeCordial.labelF 0)
      (KnodelPrimeCordial.labelF (n - 1)) := by
  have h0 : KnodelPrimeCordial.labelF 0 = 2 := by decide
  have hm : (n - 1) % 12 = 5 := by omega
  have h1 : KnodelPrimeCordial.labelF (n - 1) = n := by
    unfold KnodelPrimeCordial.labelF
    rw [hm]
    show n - 1 + 1 = n
    omega
  rw [h0, h1, Nat.coprime_two_left, Nat.not_odd_iff_even]
  exact ⟨n / 2, by omega⟩

