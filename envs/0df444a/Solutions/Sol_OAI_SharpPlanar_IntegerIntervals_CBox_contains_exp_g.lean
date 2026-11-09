-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:24:31.539047+00:00
-- url     : https://prove2.me/submissions/0f389183-8e72-4b31-8f07-9eccd4a3689b

import Mathlib
import Definitions.Def_OAIQ098G075
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_horner_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_squareIter_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_exp_from_horner_g

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

lemma CBox.widen_check (a : CBox) (k : ℤ) : a.WidenCheck (a.widen k) k := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩

lemma CBox.contains_exp_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ)
    (hn : (a.scale 1 (2^k)).NormCheck 1) : (a.exp k).Contains (Complex.exp z) := by
  have he := exp_from_horner_g (CBox.contains_scale_g hz 1 (2^k) (by positivity)) hn
    (CBox.contains_horner_g (CBox.contains_scale_g hz 1 (2^k) (by positivity)) 0 32)
    (CBox.widen_check _ 1)
  have hs := CBox.contains_squareIter_g he k
  rw [← Complex.exp_nat_mul] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  field_simp


end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g_oai
