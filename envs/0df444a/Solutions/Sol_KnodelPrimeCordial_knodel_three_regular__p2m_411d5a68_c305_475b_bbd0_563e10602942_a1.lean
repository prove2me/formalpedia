-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:24:34.866952+00:00
-- url     : https://prove2.me/submissions/e9c997b7-96cf-4ff7-9d55-774aa1d0b323

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_knodel_three_regular_side0__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
import Theorems.Thm_KnodelPrimeCordial_knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n)
    (v : Fin 2 × Fin (n / 2)) : (KnodelPrimeCordial.knodel 3 n).degree v = 3 := by
  rcases v with ⟨s, j⟩
  fin_cases s
  · simpa using
      KnodelPrimeCordial.knodel_three_regular_side0__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
        n hn h10 j
  · simpa using
      KnodelPrimeCordial.knodel_three_regular_side1__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
        n hn h10 j
