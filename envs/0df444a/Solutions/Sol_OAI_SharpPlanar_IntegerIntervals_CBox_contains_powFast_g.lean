-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:44.77117+00:00
-- url     : https://prove2.me/submissions/adc3fb06-5e99-4c32-b5ea-1d5ede1b25df

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_powFast_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powFast k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powFast] using CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    simp only [CBox.powFast]
    split_ifs with h0 h1 h2
    · subst n
      simpa using CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num)
    · subst n
      simpa using hz
    · have hh := CBox.contains_mul_g (ih (n/2) hd) (ih (n/2) hd)
      have ht : n/2+n/2=n := by omega
      simpa only [← pow_add,ht] using hh
    · have hh := CBox.contains_mul_g (CBox.contains_mul_g (ih (n/2) hd) (ih (n/2) hd)) hz
      have ht : n/2+n/2+1=n := by omega
      simpa only [← pow_add,pow_one,← pow_succ,ht] using hh

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_g_oai
