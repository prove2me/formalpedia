-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:05.903208+00:00
-- url     : https://prove2.me/submissions/3612f86f-fdae-4393-b83d-ecb1ff9b4f13

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

lemma p1_144_contains : p1_144.Contains (quadraturePoint 1 144) := by
  have ht : p1_144.t.Contains (quadraturePoint 1 144) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨144,by decide⟩).scale 1 12) = p1_144.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨144,by decide⟩
  have he : PointBox.calc p1_144.t = p1_144 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_145_contains : p1_145.Contains (quadraturePoint 1 145) := by
  have ht : p1_145.t.Contains (quadraturePoint 1 145) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨145,by decide⟩).scale 1 12) = p1_145.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨145,by decide⟩
  have he : PointBox.calc p1_145.t = p1_145 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_146_contains : p1_146.Contains (quadraturePoint 1 146) := by
  have ht : p1_146.t.Contains (quadraturePoint 1 146) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨146,by decide⟩).scale 1 12) = p1_146.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨146,by decide⟩
  have he : PointBox.calc p1_146.t = p1_146 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_147_contains : p1_147.Contains (quadraturePoint 1 147) := by
  have ht : p1_147.t.Contains (quadraturePoint 1 147) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨147,by decide⟩).scale 1 12) = p1_147.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨147,by decide⟩
  have he : PointBox.calc p1_147.t = p1_147 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_148_contains : p1_148.Contains (quadraturePoint 1 148) := by
  have ht : p1_148.t.Contains (quadraturePoint 1 148) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨148,by decide⟩).scale 1 12) = p1_148.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨148,by decide⟩
  have he : PointBox.calc p1_148.t = p1_148 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_149_contains : p1_149.Contains (quadraturePoint 1 149) := by
  have ht : p1_149.t.Contains (quadraturePoint 1 149) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨149,by decide⟩).scale 1 12) = p1_149.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨149,by decide⟩
  have he : PointBox.calc p1_149.t = p1_149 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_150_contains : p1_150.Contains (quadraturePoint 1 150) := by
  have ht : p1_150.t.Contains (quadraturePoint 1 150) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨150,by decide⟩).scale 1 12) = p1_150.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨150,by decide⟩
  have he : PointBox.calc p1_150.t = p1_150 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_151_contains : p1_151.Contains (quadraturePoint 1 151) := by
  have ht : p1_151.t.Contains (quadraturePoint 1 151) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨151,by decide⟩).scale 1 12) = p1_151.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨151,by decide⟩
  have he : PointBox.calc p1_151.t = p1_151 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_152_contains : p1_152.Contains (quadraturePoint 1 152) := by
  have ht : p1_152.t.Contains (quadraturePoint 1 152) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨152,by decide⟩).scale 1 12) = p1_152.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨152,by decide⟩
  have he : PointBox.calc p1_152.t = p1_152 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_153_contains : p1_153.Contains (quadraturePoint 1 153) := by
  have ht : p1_153.t.Contains (quadraturePoint 1 153) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨153,by decide⟩).scale 1 12) = p1_153.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨153,by decide⟩
  have he : PointBox.calc p1_153.t = p1_153 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_154_contains : p1_154.Contains (quadraturePoint 1 154) := by
  have ht : p1_154.t.Contains (quadraturePoint 1 154) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨154,by decide⟩).scale 1 12) = p1_154.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨154,by decide⟩
  have he : PointBox.calc p1_154.t = p1_154 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_155_contains : p1_155.Contains (quadraturePoint 1 155) := by
  have ht : p1_155.t.Contains (quadraturePoint 1 155) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨155,by decide⟩).scale 1 12) = p1_155.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨155,by decide⟩
  have he : PointBox.calc p1_155.t = p1_155 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_156_contains : p1_156.Contains (quadraturePoint 1 156) := by
  have ht : p1_156.t.Contains (quadraturePoint 1 156) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨156,by decide⟩).scale 1 12) = p1_156.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨156,by decide⟩
  have he : PointBox.calc p1_156.t = p1_156 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_157_contains : p1_157.Contains (quadraturePoint 1 157) := by
  have ht : p1_157.t.Contains (quadraturePoint 1 157) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨157,by decide⟩).scale 1 12) = p1_157.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨157,by decide⟩
  have he : PointBox.calc p1_157.t = p1_157 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_158_contains : p1_158.Contains (quadraturePoint 1 158) := by
  have ht : p1_158.t.Contains (quadraturePoint 1 158) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨158,by decide⟩).scale 1 12) = p1_158.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨158,by decide⟩
  have he : PointBox.calc p1_158.t = p1_158 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_159_contains : p1_159.Contains (quadraturePoint 1 159) := by
  have ht : p1_159.t.Contains (quadraturePoint 1 159) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨159,by decide⟩).scale 1 12) = p1_159.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨159,by decide⟩
  have he : PointBox.calc p1_159.t = p1_159 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_9_contains_g_oai (k : Fin 16) : (row1_9 k).Contains (quadraturePoint 1 (144+k.val)) := by
  fin_cases k
  · exact p1_144_contains
  · exact p1_145_contains
  · exact p1_146_contains
  · exact p1_147_contains
  · exact p1_148_contains
  · exact p1_149_contains
  · exact p1_150_contains
  · exact p1_151_contains
  · exact p1_152_contains
  · exact p1_153_contains
  · exact p1_154_contains
  · exact p1_155_contains
  · exact p1_156_contains
  · exact p1_157_contains
  · exact p1_158_contains
  · exact p1_159_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_9_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_9_contains_g_oai
