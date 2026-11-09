-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:36.477299+00:00
-- url     : https://prove2.me/submissions/8ee8ebe2-fccc-49de-9701-1b9452c8f225

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

lemma p0_128_contains : p0_128.Contains (quadraturePoint 0 128) := by
  have ht : p0_128.t.Contains (quadraturePoint 0 128) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨128,by decide⟩).scale 1 12) = p0_128.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨128,by decide⟩
  have he : PointBox.calc p0_128.t = p0_128 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_129_contains : p0_129.Contains (quadraturePoint 0 129) := by
  have ht : p0_129.t.Contains (quadraturePoint 0 129) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨129,by decide⟩).scale 1 12) = p0_129.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨129,by decide⟩
  have he : PointBox.calc p0_129.t = p0_129 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_130_contains : p0_130.Contains (quadraturePoint 0 130) := by
  have ht : p0_130.t.Contains (quadraturePoint 0 130) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨130,by decide⟩).scale 1 12) = p0_130.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨130,by decide⟩
  have he : PointBox.calc p0_130.t = p0_130 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_131_contains : p0_131.Contains (quadraturePoint 0 131) := by
  have ht : p0_131.t.Contains (quadraturePoint 0 131) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨131,by decide⟩).scale 1 12) = p0_131.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨131,by decide⟩
  have he : PointBox.calc p0_131.t = p0_131 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_132_contains : p0_132.Contains (quadraturePoint 0 132) := by
  have ht : p0_132.t.Contains (quadraturePoint 0 132) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨132,by decide⟩).scale 1 12) = p0_132.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨132,by decide⟩
  have he : PointBox.calc p0_132.t = p0_132 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_133_contains : p0_133.Contains (quadraturePoint 0 133) := by
  have ht : p0_133.t.Contains (quadraturePoint 0 133) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨133,by decide⟩).scale 1 12) = p0_133.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨133,by decide⟩
  have he : PointBox.calc p0_133.t = p0_133 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_134_contains : p0_134.Contains (quadraturePoint 0 134) := by
  have ht : p0_134.t.Contains (quadraturePoint 0 134) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨134,by decide⟩).scale 1 12) = p0_134.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨134,by decide⟩
  have he : PointBox.calc p0_134.t = p0_134 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_135_contains : p0_135.Contains (quadraturePoint 0 135) := by
  have ht : p0_135.t.Contains (quadraturePoint 0 135) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨135,by decide⟩).scale 1 12) = p0_135.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨135,by decide⟩
  have he : PointBox.calc p0_135.t = p0_135 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_136_contains : p0_136.Contains (quadraturePoint 0 136) := by
  have ht : p0_136.t.Contains (quadraturePoint 0 136) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨136,by decide⟩).scale 1 12) = p0_136.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨136,by decide⟩
  have he : PointBox.calc p0_136.t = p0_136 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_137_contains : p0_137.Contains (quadraturePoint 0 137) := by
  have ht : p0_137.t.Contains (quadraturePoint 0 137) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨137,by decide⟩).scale 1 12) = p0_137.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨137,by decide⟩
  have he : PointBox.calc p0_137.t = p0_137 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_138_contains : p0_138.Contains (quadraturePoint 0 138) := by
  have ht : p0_138.t.Contains (quadraturePoint 0 138) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨138,by decide⟩).scale 1 12) = p0_138.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨138,by decide⟩
  have he : PointBox.calc p0_138.t = p0_138 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_139_contains : p0_139.Contains (quadraturePoint 0 139) := by
  have ht : p0_139.t.Contains (quadraturePoint 0 139) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨139,by decide⟩).scale 1 12) = p0_139.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨139,by decide⟩
  have he : PointBox.calc p0_139.t = p0_139 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_140_contains : p0_140.Contains (quadraturePoint 0 140) := by
  have ht : p0_140.t.Contains (quadraturePoint 0 140) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨140,by decide⟩).scale 1 12) = p0_140.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨140,by decide⟩
  have he : PointBox.calc p0_140.t = p0_140 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_141_contains : p0_141.Contains (quadraturePoint 0 141) := by
  have ht : p0_141.t.Contains (quadraturePoint 0 141) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨141,by decide⟩).scale 1 12) = p0_141.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨141,by decide⟩
  have he : PointBox.calc p0_141.t = p0_141 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_142_contains : p0_142.Contains (quadraturePoint 0 142) := by
  have ht : p0_142.t.Contains (quadraturePoint 0 142) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨142,by decide⟩).scale 1 12) = p0_142.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨142,by decide⟩
  have he : PointBox.calc p0_142.t = p0_142 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_143_contains : p0_143.Contains (quadraturePoint 0 143) := by
  have ht : p0_143.t.Contains (quadraturePoint 0 143) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨143,by decide⟩).scale 1 12) = p0_143.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨143,by decide⟩
  have he : PointBox.calc p0_143.t = p0_143 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_8_contains_g_oai (k : Fin 16) : (row0_8 k).Contains (quadraturePoint 0 (128+k.val)) := by
  fin_cases k
  · exact p0_128_contains
  · exact p0_129_contains
  · exact p0_130_contains
  · exact p0_131_contains
  · exact p0_132_contains
  · exact p0_133_contains
  · exact p0_134_contains
  · exact p0_135_contains
  · exact p0_136_contains
  · exact p0_137_contains
  · exact p0_138_contains
  · exact p0_139_contains
  · exact p0_140_contains
  · exact p0_141_contains
  · exact p0_142_contains
  · exact p0_143_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_8_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_8_contains_g_oai
