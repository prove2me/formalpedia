-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.qiBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:35:23.79621+00:00
-- url     : https://prove2.me/submissions/4bf4fe76-9b6e-423f-9c05-d25ffe20a2eb

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_inv_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_Q_0_e
import Theorems.Thm_OAI_SharpPlanar_Q_1_e
import Theorems.Thm_OAI_SharpPlanar_Q_3_e
import Theorems.Thm_OAI_SharpPlanar_Q_4_e
import Theorems.Thm_OAI_SharpPlanar_Q_7_e
import Theorems.Thm_OAI_SharpPlanar_Q_9_e

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

lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma RBox.contains_add {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains_e hx hy (RBox.add_check _ _)
lemma RBox.contains_mul {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains_e hx hy (RBox.mul_check_e _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

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
  have hp := RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e piBounds_contains_e) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat_e 2 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e (-2) 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma qLarge_contains : qLarge.Contains ((2*Real.pi^2/3)*(2+2*b)) := by
  have hp := RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e piBounds_contains_e) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat_e 2 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e 2 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring_nf <;> simp)
lemma qBase_contains : qBase.Contains (Real.pi^2/3) := by
  convert RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e piBounds_contains_e) 1 3 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qBase] <;> ring)

lemma qBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qBox n).Contains (Q n) := by
  have hh : Q n = Q (n%12) := by simp [Q]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn <;> simp only [hn, qBox] <;>
    norm_num only at *
  · simpa [Q_0_e,hn,qBox] using qBase_contains
  · simpa [Q_1_e,hn,qBox] using qSmall_contains
  · simpa [Q_3_e,hn,qBox] using qSmall_contains
  · simpa [Q_4_e,hn,qBox] using qBase_contains
  · simpa [Q_7_e,hn,qBox] using qLarge_contains
  · simpa [Q_9_e,hn,qBox] using qLarge_contains
lemma qiBox_contains_e_oai (n : ℕ) (hn : n%12 ∈ residues) : (qiBox n).Contains (Q n)⁻¹ := by
  apply RBox.inv_contains_e (qBox_contains n hn)
  unfold qiBox qBox
  split <;> (try split) <;> decide +kernel

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.qiBox_contains_e_oai := @OAI.SharpPlanar.Numerical.qiBox_contains_e_oai
