-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.qiBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:12:52.714654+00:00
-- url     : https://prove2.me/submissions/c29b804f-9a31-42e2-870a-d0f558826fe3

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G098
import Definitions.Def_OAIQ098G099
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_inv_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_Q_0_g
import Theorems.Thm_OAI_SharpPlanar_Q_1_g
import Theorems.Thm_OAI_SharpPlanar_Q_3_g
import Theorems.Thm_OAI_SharpPlanar_Q_4_g
import Theorems.Thm_OAI_SharpPlanar_Q_7_g
import Theorems.Thm_OAI_SharpPlanar_Q_9_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma qSmall_contains : qSmall.Contains ((2*Real.pi^2/3)*(2-2*b)) := by
  have hp := RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g piBounds_contains_g) 2 3 (by norm_num)
  have hb := RBox.contains_add_g (RBox.contains_rat_g 2 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g (-2) 1 (by norm_num))
  convert RBox.contains_mul_g hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma qLarge_contains : qLarge.Contains ((2*Real.pi^2/3)*(2+2*b)) := by
  have hp := RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g piBounds_contains_g) 2 3 (by norm_num)
  have hb := RBox.contains_add_g (RBox.contains_rat_g 2 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g 2 1 (by norm_num))
  convert RBox.contains_mul_g hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring_nf <;> simp)
lemma qBase_contains : qBase.Contains (Real.pi^2/3) := by
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g piBounds_contains_g) 1 3 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qBase] <;> ring)

lemma qBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qBox n).Contains (Q n) := by
  have hh : Q n = Q (n%12) := by simp [Q]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn <;> simp only [hn, qBox] <;>
    norm_num only at *
  · simpa [Q_0_g,hn,qBox] using qBase_contains
  · simpa [Q_1_g,hn,qBox] using qSmall_contains
  · simpa [Q_3_g,hn,qBox] using qSmall_contains
  · simpa [Q_4_g,hn,qBox] using qBase_contains
  · simpa [Q_7_g,hn,qBox] using qLarge_contains
  · simpa [Q_9_g,hn,qBox] using qLarge_contains
lemma qiBox_contains_g_oai (n : ℕ) (hn : n%12 ∈ residues) : (qiBox n).Contains (Q n)⁻¹ := by
  apply RBox.inv_contains_g (qBox_contains n hn)
  unfold qiBox qBox
  split <;> (try split) <;> decide +kernel

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.qiBox_contains_g_oai := @OAI.SharpPlanar.Numerical.qiBox_contains_g_oai
