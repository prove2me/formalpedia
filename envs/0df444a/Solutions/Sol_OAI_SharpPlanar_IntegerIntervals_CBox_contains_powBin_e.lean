-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:22:18.721879+00:00
-- url     : https://prove2.me/submissions/a24320a9-17b5-46f7-99db-5fb9796c1c40

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e

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

lemma CBox.contains_powBin_e_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powBin k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powBin] using CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    have hb := CBox.contains_mul_e (ih (n/2) hd) (ih (n/2) hd)
    rw [← pow_add] at hb
    dsimp only [CBox.powBin]
    split_ifs with h
    · convert hb using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega
    · have hh := CBox.contains_mul_e hb hz
      rw [← pow_succ] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_powBin_e_oai
