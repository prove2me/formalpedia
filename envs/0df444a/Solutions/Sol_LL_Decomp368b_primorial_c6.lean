-- Prove2me | solution 1 for LL_Decomp368b.primorial_c6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:12:23.243733+00:00
-- url     : https://prove2.me/submissions/9f6a2f1d-bc23-4029-8446-19a91fe4e989

import Mathlib.NumberTheory.Primorial
import Theorems.Thm_PrimorialRange_bound_32000000_34129386
import Theorems.Thm_PrimorialRange_bound_34129386_42496200
import Theorems.Thm_PrimorialRange_bound_42496200_52597756
import Theorems.Thm_PrimorialRange_bound_52597756_60984648
import Theorems.Thm_PrimorialRange_bound_60984648_69355435
import Theorems.Thm_PrimorialRange_bound_69355435_77727216
import Theorems.Thm_PrimorialRange_bound_77727216_87458565
import Theorems.Thm_PrimorialRange_bound_87458565_100000000

theorem solution (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases h0 : n ≤ 34129386
  · exact PrimorialRange.bound_32000000_34129386 n hn h0
  by_cases h1 : n ≤ 42496200
  · exact PrimorialRange.bound_34129386_42496200 n (by omega) h1
  by_cases h2 : n ≤ 52597756
  · exact PrimorialRange.bound_42496200_52597756 n (by omega) h2
  by_cases h3 : n ≤ 60984648
  · exact PrimorialRange.bound_52597756_60984648 n (by omega) h3
  by_cases h4 : n ≤ 69355435
  · exact PrimorialRange.bound_60984648_69355435 n (by omega) h4
  by_cases h5 : n ≤ 77727216
  · exact PrimorialRange.bound_69355435_77727216 n (by omega) h5
  by_cases h6 : n ≤ 87458565
  · exact PrimorialRange.bound_77727216_87458565 n (by omega) h6
  exact PrimorialRange.bound_87458565_100000000 n (by omega) hn'
