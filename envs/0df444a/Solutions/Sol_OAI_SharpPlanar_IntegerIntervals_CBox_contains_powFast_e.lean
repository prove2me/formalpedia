-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:22:42.141573+00:00
-- url     : https://prove2.me/submissions/b405a6f2-67e1-4a2a-af2a-9506217f42a0

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_powFast_e_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powFast k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powFast] using CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    simp only [CBox.powFast]
    split_ifs with h0 h1 h2
    · subst n
      simpa using CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num)
    · subst n
      simpa using hz
    · have hh := CBox.contains_mul_e (ih (n/2) hd) (ih (n/2) hd)
      have ht : n/2+n/2=n := by omega
      simpa only [← pow_add,ht] using hh
    · have hh := CBox.contains_mul_e (CBox.contains_mul_e (ih (n/2) hd) (ih (n/2) hd)) hz
      have ht : n/2+n/2+1=n := by omega
      simpa only [← pow_add,pow_one,← pow_succ,ht] using hh

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powFast_e_oai
