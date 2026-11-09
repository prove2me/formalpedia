-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:24.088205+00:00
-- url     : https://prove2.me/submissions/d56dbd52-87e7-4f32-9f4d-257e22501d31

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

lemma p1_112_contains : p1_112.Contains (quadraturePoint 1 112) := by
  have ht : p1_112.t.Contains (quadraturePoint 1 112) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨112,by decide⟩).scale 1 12) = p1_112.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨112,by decide⟩
  have he : PointBox.calc p1_112.t = p1_112 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_113_contains : p1_113.Contains (quadraturePoint 1 113) := by
  have ht : p1_113.t.Contains (quadraturePoint 1 113) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨113,by decide⟩).scale 1 12) = p1_113.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨113,by decide⟩
  have he : PointBox.calc p1_113.t = p1_113 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_114_contains : p1_114.Contains (quadraturePoint 1 114) := by
  have ht : p1_114.t.Contains (quadraturePoint 1 114) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨114,by decide⟩).scale 1 12) = p1_114.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨114,by decide⟩
  have he : PointBox.calc p1_114.t = p1_114 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_115_contains : p1_115.Contains (quadraturePoint 1 115) := by
  have ht : p1_115.t.Contains (quadraturePoint 1 115) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨115,by decide⟩).scale 1 12) = p1_115.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨115,by decide⟩
  have he : PointBox.calc p1_115.t = p1_115 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_116_contains : p1_116.Contains (quadraturePoint 1 116) := by
  have ht : p1_116.t.Contains (quadraturePoint 1 116) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨116,by decide⟩).scale 1 12) = p1_116.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨116,by decide⟩
  have he : PointBox.calc p1_116.t = p1_116 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_117_contains : p1_117.Contains (quadraturePoint 1 117) := by
  have ht : p1_117.t.Contains (quadraturePoint 1 117) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨117,by decide⟩).scale 1 12) = p1_117.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨117,by decide⟩
  have he : PointBox.calc p1_117.t = p1_117 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_118_contains : p1_118.Contains (quadraturePoint 1 118) := by
  have ht : p1_118.t.Contains (quadraturePoint 1 118) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨118,by decide⟩).scale 1 12) = p1_118.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨118,by decide⟩
  have he : PointBox.calc p1_118.t = p1_118 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_119_contains : p1_119.Contains (quadraturePoint 1 119) := by
  have ht : p1_119.t.Contains (quadraturePoint 1 119) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨119,by decide⟩).scale 1 12) = p1_119.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨119,by decide⟩
  have he : PointBox.calc p1_119.t = p1_119 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_120_contains : p1_120.Contains (quadraturePoint 1 120) := by
  have ht : p1_120.t.Contains (quadraturePoint 1 120) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨120,by decide⟩).scale 1 12) = p1_120.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨120,by decide⟩
  have he : PointBox.calc p1_120.t = p1_120 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_121_contains : p1_121.Contains (quadraturePoint 1 121) := by
  have ht : p1_121.t.Contains (quadraturePoint 1 121) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨121,by decide⟩).scale 1 12) = p1_121.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨121,by decide⟩
  have he : PointBox.calc p1_121.t = p1_121 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_122_contains : p1_122.Contains (quadraturePoint 1 122) := by
  have ht : p1_122.t.Contains (quadraturePoint 1 122) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨122,by decide⟩).scale 1 12) = p1_122.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨122,by decide⟩
  have he : PointBox.calc p1_122.t = p1_122 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_123_contains : p1_123.Contains (quadraturePoint 1 123) := by
  have ht : p1_123.t.Contains (quadraturePoint 1 123) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨123,by decide⟩).scale 1 12) = p1_123.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨123,by decide⟩
  have he : PointBox.calc p1_123.t = p1_123 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_124_contains : p1_124.Contains (quadraturePoint 1 124) := by
  have ht : p1_124.t.Contains (quadraturePoint 1 124) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨124,by decide⟩).scale 1 12) = p1_124.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨124,by decide⟩
  have he : PointBox.calc p1_124.t = p1_124 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_125_contains : p1_125.Contains (quadraturePoint 1 125) := by
  have ht : p1_125.t.Contains (quadraturePoint 1 125) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨125,by decide⟩).scale 1 12) = p1_125.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨125,by decide⟩
  have he : PointBox.calc p1_125.t = p1_125 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_126_contains : p1_126.Contains (quadraturePoint 1 126) := by
  have ht : p1_126.t.Contains (quadraturePoint 1 126) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨126,by decide⟩).scale 1 12) = p1_126.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨126,by decide⟩
  have he : PointBox.calc p1_126.t = p1_126 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_127_contains : p1_127.Contains (quadraturePoint 1 127) := by
  have ht : p1_127.t.Contains (quadraturePoint 1 127) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨127,by decide⟩).scale 1 12) = p1_127.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨127,by decide⟩
  have he : PointBox.calc p1_127.t = p1_127 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_7_contains_g_oai (k : Fin 16) : (row1_7 k).Contains (quadraturePoint 1 (112+k.val)) := by
  fin_cases k
  · exact p1_112_contains
  · exact p1_113_contains
  · exact p1_114_contains
  · exact p1_115_contains
  · exact p1_116_contains
  · exact p1_117_contains
  · exact p1_118_contains
  · exact p1_119_contains
  · exact p1_120_contains
  · exact p1_121_contains
  · exact p1_122_contains
  · exact p1_123_contains
  · exact p1_124_contains
  · exact p1_125_contains
  · exact p1_126_contains
  · exact p1_127_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_7_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_7_contains_g_oai
