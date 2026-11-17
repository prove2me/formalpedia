-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_label_range__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:38:20.091901+00:00
-- url     : https://prove2.me/submissions/4e58fdb3-d25b-4a24-84ea-bd1b43edc7e7

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    ∀ i : Fin n,
      (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val) i ∈
        Set.Icc 1 n := by
  intro i
  let k := i.val
  have hk : k < n := i.isLt
  have hdivk : k % 12 + 12 * (k / 12) = k := Nat.mod_add_div k 12
  have hdivn : n % 12 + 12 * (n / 12) = n := Nat.mod_add_div n 12
  change (if k = n - 3 then k + 3 else KnodelPrimeCordial.labelF k) ∈ Set.Icc 1 n
  by_cases hs : k = n - 3
  · simp [hs]
    omega
  · simp [hs, Set.mem_Icc]
    unfold KnodelPrimeCordial.labelF
    have hrem : k % 12 < 12 := Nat.mod_lt _ (by omega)
    interval_cases r : k % 12 <;> simp [r] <;> omega
