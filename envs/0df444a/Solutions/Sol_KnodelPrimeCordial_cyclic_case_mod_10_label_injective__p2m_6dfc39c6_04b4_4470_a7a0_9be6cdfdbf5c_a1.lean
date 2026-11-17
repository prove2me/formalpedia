-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:37:27.837407+00:00
-- url     : https://prove2.me/submissions/a2d57087-8f6d-47b5-ba68-c04b80cce3b0

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Function.Injective
      (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val) := by
  have hlabel : Function.Injective KnodelPrimeCordial.labelF := by
    intro x y hxy
    have hxlt : x % 12 < 12 := Nat.mod_lt x (by omega)
    have hylt : y % 12 < 12 := Nat.mod_lt y (by omega)
    interval_cases hx : x % 12 <;> interval_cases hy : y % 12 <;>
      simp [KnodelPrimeCordial.labelF, hx, hy] at hxy <;> omega
  have hboundary : KnodelPrimeCordial.labelF (n + 1) = n := by
    have hres : (n + 1) % 12 = 11 := by omega
    simp [KnodelPrimeCordial.labelF, hres]
  intro a b hab
  by_cases ha : a.val = n - 3
  · by_cases hb : b.val = n - 3
    · apply Fin.ext
      exact ha.trans hb.symm
    · have hab' : a.val + 3 = KnodelPrimeCordial.labelF b.val := by
        simpa [ha, hb] using hab
      have hval : a.val + 3 = n := by omega
      have hbval : KnodelPrimeCordial.labelF b.val = KnodelPrimeCordial.labelF (n + 1) := by
        rw [hboundary]
        omega
      have : b.val = n + 1 := hlabel hbval
      omega
  · by_cases hb : b.val = n - 3
    · have hab' : KnodelPrimeCordial.labelF a.val = b.val + 3 := by
        simpa [ha, hb] using hab
      have hval : b.val + 3 = n := by omega
      have haval : KnodelPrimeCordial.labelF a.val = KnodelPrimeCordial.labelF (n + 1) := by
        rw [hboundary]
        omega
      have : a.val = n + 1 := hlabel haval
      omega
    · have hab' : KnodelPrimeCordial.labelF a.val = KnodelPrimeCordial.labelF b.val := by
        simpa [ha, hb] using hab
      apply Fin.ext
      exact hlabel hab'
