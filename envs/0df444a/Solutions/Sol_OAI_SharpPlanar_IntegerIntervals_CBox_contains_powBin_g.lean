-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:54.154316+00:00
-- url     : https://prove2.me/submissions/175327a0-c8ec-4414-aab3-99cb04e21b01

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_powBin_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powBin k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powBin] using CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    have hb := CBox.contains_mul_g (ih (n/2) hd) (ih (n/2) hd)
    rw [← pow_add] at hb
    dsimp only [CBox.powBin]
    split_ifs with h
    · convert hb using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega
    · have hh := CBox.contains_mul_g hb hz
      rw [← pow_succ] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_g_oai
