-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:11.115209+00:00
-- url     : https://prove2.me/submissions/a57ce1db-6b3d-4dd0-9f21-4e5628b5aa67

import Mathlib
import Definitions.Def_OAIQ098G020
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

lemma p5_112_contains : p5_112.Contains (quadraturePoint 5 112) := by
  have ht : p5_112.t.Contains (quadraturePoint 5 112) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨112,by decide⟩).scale 1 12) = p5_112.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨112,by decide⟩
  have he : PointBox.calc p5_112.t = p5_112 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_113_contains : p5_113.Contains (quadraturePoint 5 113) := by
  have ht : p5_113.t.Contains (quadraturePoint 5 113) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨113,by decide⟩).scale 1 12) = p5_113.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨113,by decide⟩
  have he : PointBox.calc p5_113.t = p5_113 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_114_contains : p5_114.Contains (quadraturePoint 5 114) := by
  have ht : p5_114.t.Contains (quadraturePoint 5 114) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨114,by decide⟩).scale 1 12) = p5_114.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨114,by decide⟩
  have he : PointBox.calc p5_114.t = p5_114 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_115_contains : p5_115.Contains (quadraturePoint 5 115) := by
  have ht : p5_115.t.Contains (quadraturePoint 5 115) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨115,by decide⟩).scale 1 12) = p5_115.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨115,by decide⟩
  have he : PointBox.calc p5_115.t = p5_115 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_116_contains : p5_116.Contains (quadraturePoint 5 116) := by
  have ht : p5_116.t.Contains (quadraturePoint 5 116) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨116,by decide⟩).scale 1 12) = p5_116.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨116,by decide⟩
  have he : PointBox.calc p5_116.t = p5_116 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_117_contains : p5_117.Contains (quadraturePoint 5 117) := by
  have ht : p5_117.t.Contains (quadraturePoint 5 117) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨117,by decide⟩).scale 1 12) = p5_117.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨117,by decide⟩
  have he : PointBox.calc p5_117.t = p5_117 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_118_contains : p5_118.Contains (quadraturePoint 5 118) := by
  have ht : p5_118.t.Contains (quadraturePoint 5 118) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨118,by decide⟩).scale 1 12) = p5_118.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨118,by decide⟩
  have he : PointBox.calc p5_118.t = p5_118 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_119_contains : p5_119.Contains (quadraturePoint 5 119) := by
  have ht : p5_119.t.Contains (quadraturePoint 5 119) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨119,by decide⟩).scale 1 12) = p5_119.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨119,by decide⟩
  have he : PointBox.calc p5_119.t = p5_119 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_120_contains : p5_120.Contains (quadraturePoint 5 120) := by
  have ht : p5_120.t.Contains (quadraturePoint 5 120) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨120,by decide⟩).scale 1 12) = p5_120.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨120,by decide⟩
  have he : PointBox.calc p5_120.t = p5_120 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_121_contains : p5_121.Contains (quadraturePoint 5 121) := by
  have ht : p5_121.t.Contains (quadraturePoint 5 121) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨121,by decide⟩).scale 1 12) = p5_121.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨121,by decide⟩
  have he : PointBox.calc p5_121.t = p5_121 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_122_contains : p5_122.Contains (quadraturePoint 5 122) := by
  have ht : p5_122.t.Contains (quadraturePoint 5 122) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨122,by decide⟩).scale 1 12) = p5_122.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨122,by decide⟩
  have he : PointBox.calc p5_122.t = p5_122 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_123_contains : p5_123.Contains (quadraturePoint 5 123) := by
  have ht : p5_123.t.Contains (quadraturePoint 5 123) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨123,by decide⟩).scale 1 12) = p5_123.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨123,by decide⟩
  have he : PointBox.calc p5_123.t = p5_123 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_124_contains : p5_124.Contains (quadraturePoint 5 124) := by
  have ht : p5_124.t.Contains (quadraturePoint 5 124) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨124,by decide⟩).scale 1 12) = p5_124.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨124,by decide⟩
  have he : PointBox.calc p5_124.t = p5_124 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_125_contains : p5_125.Contains (quadraturePoint 5 125) := by
  have ht : p5_125.t.Contains (quadraturePoint 5 125) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨125,by decide⟩).scale 1 12) = p5_125.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨125,by decide⟩
  have he : PointBox.calc p5_125.t = p5_125 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_126_contains : p5_126.Contains (quadraturePoint 5 126) := by
  have ht : p5_126.t.Contains (quadraturePoint 5 126) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨126,by decide⟩).scale 1 12) = p5_126.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨126,by decide⟩
  have he : PointBox.calc p5_126.t = p5_126 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_127_contains : p5_127.Contains (quadraturePoint 5 127) := by
  have ht : p5_127.t.Contains (quadraturePoint 5 127) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨127,by decide⟩).scale 1 12) = p5_127.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨127,by decide⟩
  have he : PointBox.calc p5_127.t = p5_127 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_7_contains_g_oai (k : Fin 16) : (row5_7 k).Contains (quadraturePoint 5 (112+k.val)) := by
  fin_cases k
  · exact p5_112_contains
  · exact p5_113_contains
  · exact p5_114_contains
  · exact p5_115_contains
  · exact p5_116_contains
  · exact p5_117_contains
  · exact p5_118_contains
  · exact p5_119_contains
  · exact p5_120_contains
  · exact p5_121_contains
  · exact p5_122_contains
  · exact p5_123_contains
  · exact p5_124_contains
  · exact p5_125_contains
  · exact p5_126_contains
  · exact p5_127_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_7_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_7_contains_g_oai
