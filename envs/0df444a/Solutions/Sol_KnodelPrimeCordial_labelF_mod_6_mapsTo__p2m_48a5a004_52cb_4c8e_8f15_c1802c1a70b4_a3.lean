-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:20:23.51128+00:00
-- url     : https://prove2.me/submissions/7a4b5968-db37-4eee-822a-79d3b21c25b1

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.MapsTo KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by
  intro i hi
  rcases hi with ⟨hi0, hiupper⟩
  have hres : i % 12 < 12 := Nat.mod_lt i (by omega)
  interval_cases hcase : i % 12 <;>
    simp [KnodelPrimeCordial.labelF, hcase] <;> omega
