-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row3_8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:47.919482+00:00
-- url     : https://prove2.me/submissions/0b9dd42e-bb5e-4ec6-a8b3-0138cc498c0e

import Mathlib
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar

lemma rootPhase_periodic (n : ℕ) : rootPhase (n+1024) = rootPhase n := by
  unfold rootPhase
  have heq : Complex.I*Real.pi*(((n+1024:ℕ):ℂ)/512) =
    Complex.I*Real.pi*((n:ℂ)/512)+(2*Real.pi*Complex.I) := by push_cast <;> ring
  rw [heq,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma rootPhase_mod (n : ℕ) : rootPhase (n%1024) = rootPhase n := by
  have hp : Function.Periodic rootPhase 1024 := rootPhase_periodic
  exact hp.map_mod_nat n

lemma rootPhase_cos (n : ℕ) : (rootPhase n).re = Real.cos (Real.pi*((n:ℝ)/512)) := by
  unfold rootPhase
  rw [Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,
    Complex.natCast_im,zero_mul,mul_zero,sub_zero,zero_add,one_mul,
    zero_div,Real.exp_zero]


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
open IntegerIntervals

lemma fejerNode_root (v : ℕ) : fejerNode v = (rootPhase (2*v+1)).re := by
  rw [rootPhase_cos]
  unfold fejerNode fejerAngle
  congr 1
  push_cast
  ring

end SharpPlanar

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma rootLookup_contains (n : ℕ) : (rootLookup n).Contains (rootPhase (n%1024)) := by
  have he : 32*((n%1024)/32)+n%32 = n%1024 := by omega
  simpa only [rootLookup,he] using rootRows_contains_g ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

lemma nodeLookup_contains (n : Fin 256) : (nodeLookup n).Contains (fejerNode n.val) := by
  have hh := (rootLookup_contains (2*n.val+1)).1
  rw [rootPhase_mod,← fejerNode_root] at hh
  exact hh
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
lemma quadraturePoint_contains (j : ℕ) (v : Fin 256) :
    ((RBox.rat (2*(j:ℤ)+1) 12).add ((nodeLookup v).scale 1 12)).Contains
      (quadraturePoint j v.val) := by
  have hh := RBox.contains_add_g (RBox.contains_rat_g (2*(j:ℤ)+1) 12 (by norm_num))
    (RBox.contains_scale_g (nodeLookup_contains v) 1 12 (by norm_num))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold quadraturePoint
  push_cast
  ring

lemma p3_128_contains : p3_128.Contains (quadraturePoint 3 128) := by
  have ht : p3_128.t.Contains (quadraturePoint 3 128) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨128,by decide⟩).scale 1 12) = p3_128.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨128,by decide⟩
  have he : PointBox.calc p3_128.t = p3_128 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_129_contains : p3_129.Contains (quadraturePoint 3 129) := by
  have ht : p3_129.t.Contains (quadraturePoint 3 129) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨129,by decide⟩).scale 1 12) = p3_129.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨129,by decide⟩
  have he : PointBox.calc p3_129.t = p3_129 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_130_contains : p3_130.Contains (quadraturePoint 3 130) := by
  have ht : p3_130.t.Contains (quadraturePoint 3 130) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨130,by decide⟩).scale 1 12) = p3_130.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨130,by decide⟩
  have he : PointBox.calc p3_130.t = p3_130 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_131_contains : p3_131.Contains (quadraturePoint 3 131) := by
  have ht : p3_131.t.Contains (quadraturePoint 3 131) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨131,by decide⟩).scale 1 12) = p3_131.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨131,by decide⟩
  have he : PointBox.calc p3_131.t = p3_131 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_132_contains : p3_132.Contains (quadraturePoint 3 132) := by
  have ht : p3_132.t.Contains (quadraturePoint 3 132) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨132,by decide⟩).scale 1 12) = p3_132.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨132,by decide⟩
  have he : PointBox.calc p3_132.t = p3_132 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_133_contains : p3_133.Contains (quadraturePoint 3 133) := by
  have ht : p3_133.t.Contains (quadraturePoint 3 133) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨133,by decide⟩).scale 1 12) = p3_133.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨133,by decide⟩
  have he : PointBox.calc p3_133.t = p3_133 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_134_contains : p3_134.Contains (quadraturePoint 3 134) := by
  have ht : p3_134.t.Contains (quadraturePoint 3 134) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨134,by decide⟩).scale 1 12) = p3_134.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨134,by decide⟩
  have he : PointBox.calc p3_134.t = p3_134 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_135_contains : p3_135.Contains (quadraturePoint 3 135) := by
  have ht : p3_135.t.Contains (quadraturePoint 3 135) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨135,by decide⟩).scale 1 12) = p3_135.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨135,by decide⟩
  have he : PointBox.calc p3_135.t = p3_135 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_136_contains : p3_136.Contains (quadraturePoint 3 136) := by
  have ht : p3_136.t.Contains (quadraturePoint 3 136) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨136,by decide⟩).scale 1 12) = p3_136.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨136,by decide⟩
  have he : PointBox.calc p3_136.t = p3_136 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_137_contains : p3_137.Contains (quadraturePoint 3 137) := by
  have ht : p3_137.t.Contains (quadraturePoint 3 137) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨137,by decide⟩).scale 1 12) = p3_137.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨137,by decide⟩
  have he : PointBox.calc p3_137.t = p3_137 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_138_contains : p3_138.Contains (quadraturePoint 3 138) := by
  have ht : p3_138.t.Contains (quadraturePoint 3 138) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨138,by decide⟩).scale 1 12) = p3_138.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨138,by decide⟩
  have he : PointBox.calc p3_138.t = p3_138 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_139_contains : p3_139.Contains (quadraturePoint 3 139) := by
  have ht : p3_139.t.Contains (quadraturePoint 3 139) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨139,by decide⟩).scale 1 12) = p3_139.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨139,by decide⟩
  have he : PointBox.calc p3_139.t = p3_139 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_140_contains : p3_140.Contains (quadraturePoint 3 140) := by
  have ht : p3_140.t.Contains (quadraturePoint 3 140) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨140,by decide⟩).scale 1 12) = p3_140.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨140,by decide⟩
  have he : PointBox.calc p3_140.t = p3_140 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_141_contains : p3_141.Contains (quadraturePoint 3 141) := by
  have ht : p3_141.t.Contains (quadraturePoint 3 141) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨141,by decide⟩).scale 1 12) = p3_141.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨141,by decide⟩
  have he : PointBox.calc p3_141.t = p3_141 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_142_contains : p3_142.Contains (quadraturePoint 3 142) := by
  have ht : p3_142.t.Contains (quadraturePoint 3 142) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨142,by decide⟩).scale 1 12) = p3_142.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨142,by decide⟩
  have he : PointBox.calc p3_142.t = p3_142 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_143_contains : p3_143.Contains (quadraturePoint 3 143) := by
  have ht : p3_143.t.Contains (quadraturePoint 3 143) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨143,by decide⟩).scale 1 12) = p3_143.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨143,by decide⟩
  have he : PointBox.calc p3_143.t = p3_143 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row3_8_contains_g_oai (k : Fin 16) : (row3_8 k).Contains (quadraturePoint 3 (128+k.val)) := by
  fin_cases k
  · exact p3_128_contains
  · exact p3_129_contains
  · exact p3_130_contains
  · exact p3_131_contains
  · exact p3_132_contains
  · exact p3_133_contains
  · exact p3_134_contains
  · exact p3_135_contains
  · exact p3_136_contains
  · exact p3_137_contains
  · exact p3_138_contains
  · exact p3_139_contains
  · exact p3_140_contains
  · exact p3_141_contains
  · exact p3_142_contains
  · exact p3_143_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row3_8_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row3_8_contains_g_oai
