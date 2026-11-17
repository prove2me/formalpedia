-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:19:25.200919+00:00
-- url     : https://prove2.me/submissions/158b5563-d954-4781-be1f-9de729d7c208

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.InjOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) := by
  intro i hi j hj hij
  have hri : i % 12 < 12 := Nat.mod_lt _ (by omega)
  have hrj : j % 12 < 12 := Nat.mod_lt _ (by omega)
  interval_cases hri' : i % 12 <;> interval_cases hrj' : j % 12 <;>
    simp [KnodelPrimeCordial.labelF, hri', hrj'] at hij <;> omega
