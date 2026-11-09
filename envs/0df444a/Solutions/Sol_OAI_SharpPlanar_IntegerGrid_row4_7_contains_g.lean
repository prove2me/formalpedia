-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row4_7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:32.644464+00:00
-- url     : https://prove2.me/submissions/2bc1576b-a9a7-4fde-903b-631acdad9620

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

lemma p4_112_contains : p4_112.Contains (quadraturePoint 4 112) := by
  have ht : p4_112.t.Contains (quadraturePoint 4 112) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨112,by decide⟩).scale 1 12) = p4_112.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨112,by decide⟩
  have he : PointBox.calc p4_112.t = p4_112 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_113_contains : p4_113.Contains (quadraturePoint 4 113) := by
  have ht : p4_113.t.Contains (quadraturePoint 4 113) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨113,by decide⟩).scale 1 12) = p4_113.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨113,by decide⟩
  have he : PointBox.calc p4_113.t = p4_113 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_114_contains : p4_114.Contains (quadraturePoint 4 114) := by
  have ht : p4_114.t.Contains (quadraturePoint 4 114) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨114,by decide⟩).scale 1 12) = p4_114.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨114,by decide⟩
  have he : PointBox.calc p4_114.t = p4_114 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_115_contains : p4_115.Contains (quadraturePoint 4 115) := by
  have ht : p4_115.t.Contains (quadraturePoint 4 115) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨115,by decide⟩).scale 1 12) = p4_115.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨115,by decide⟩
  have he : PointBox.calc p4_115.t = p4_115 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_116_contains : p4_116.Contains (quadraturePoint 4 116) := by
  have ht : p4_116.t.Contains (quadraturePoint 4 116) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨116,by decide⟩).scale 1 12) = p4_116.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨116,by decide⟩
  have he : PointBox.calc p4_116.t = p4_116 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_117_contains : p4_117.Contains (quadraturePoint 4 117) := by
  have ht : p4_117.t.Contains (quadraturePoint 4 117) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨117,by decide⟩).scale 1 12) = p4_117.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨117,by decide⟩
  have he : PointBox.calc p4_117.t = p4_117 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_118_contains : p4_118.Contains (quadraturePoint 4 118) := by
  have ht : p4_118.t.Contains (quadraturePoint 4 118) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨118,by decide⟩).scale 1 12) = p4_118.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨118,by decide⟩
  have he : PointBox.calc p4_118.t = p4_118 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_119_contains : p4_119.Contains (quadraturePoint 4 119) := by
  have ht : p4_119.t.Contains (quadraturePoint 4 119) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨119,by decide⟩).scale 1 12) = p4_119.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨119,by decide⟩
  have he : PointBox.calc p4_119.t = p4_119 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_120_contains : p4_120.Contains (quadraturePoint 4 120) := by
  have ht : p4_120.t.Contains (quadraturePoint 4 120) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨120,by decide⟩).scale 1 12) = p4_120.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨120,by decide⟩
  have he : PointBox.calc p4_120.t = p4_120 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_121_contains : p4_121.Contains (quadraturePoint 4 121) := by
  have ht : p4_121.t.Contains (quadraturePoint 4 121) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨121,by decide⟩).scale 1 12) = p4_121.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨121,by decide⟩
  have he : PointBox.calc p4_121.t = p4_121 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_122_contains : p4_122.Contains (quadraturePoint 4 122) := by
  have ht : p4_122.t.Contains (quadraturePoint 4 122) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨122,by decide⟩).scale 1 12) = p4_122.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨122,by decide⟩
  have he : PointBox.calc p4_122.t = p4_122 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_123_contains : p4_123.Contains (quadraturePoint 4 123) := by
  have ht : p4_123.t.Contains (quadraturePoint 4 123) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨123,by decide⟩).scale 1 12) = p4_123.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨123,by decide⟩
  have he : PointBox.calc p4_123.t = p4_123 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_124_contains : p4_124.Contains (quadraturePoint 4 124) := by
  have ht : p4_124.t.Contains (quadraturePoint 4 124) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨124,by decide⟩).scale 1 12) = p4_124.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨124,by decide⟩
  have he : PointBox.calc p4_124.t = p4_124 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_125_contains : p4_125.Contains (quadraturePoint 4 125) := by
  have ht : p4_125.t.Contains (quadraturePoint 4 125) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨125,by decide⟩).scale 1 12) = p4_125.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨125,by decide⟩
  have he : PointBox.calc p4_125.t = p4_125 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_126_contains : p4_126.Contains (quadraturePoint 4 126) := by
  have ht : p4_126.t.Contains (quadraturePoint 4 126) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨126,by decide⟩).scale 1 12) = p4_126.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨126,by decide⟩
  have he : PointBox.calc p4_126.t = p4_126 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_127_contains : p4_127.Contains (quadraturePoint 4 127) := by
  have ht : p4_127.t.Contains (quadraturePoint 4 127) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨127,by decide⟩).scale 1 12) = p4_127.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨127,by decide⟩
  have he : PointBox.calc p4_127.t = p4_127 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row4_7_contains_g_oai (k : Fin 16) : (row4_7 k).Contains (quadraturePoint 4 (112+k.val)) := by
  fin_cases k
  · exact p4_112_contains
  · exact p4_113_contains
  · exact p4_114_contains
  · exact p4_115_contains
  · exact p4_116_contains
  · exact p4_117_contains
  · exact p4_118_contains
  · exact p4_119_contains
  · exact p4_120_contains
  · exact p4_121_contains
  · exact p4_122_contains
  · exact p4_123_contains
  · exact p4_124_contains
  · exact p4_125_contains
  · exact p4_126_contains
  · exact p4_127_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row4_7_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row4_7_contains_g_oai
