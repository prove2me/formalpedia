-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row2_10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:09.295035+00:00
-- url     : https://prove2.me/submissions/0eb47754-436d-400b-8ec3-dfd2387c2ec4

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

lemma p2_160_contains : p2_160.Contains (quadraturePoint 2 160) := by
  have ht : p2_160.t.Contains (quadraturePoint 2 160) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨160,by decide⟩).scale 1 12) = p2_160.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨160,by decide⟩
  have he : PointBox.calc p2_160.t = p2_160 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_161_contains : p2_161.Contains (quadraturePoint 2 161) := by
  have ht : p2_161.t.Contains (quadraturePoint 2 161) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨161,by decide⟩).scale 1 12) = p2_161.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨161,by decide⟩
  have he : PointBox.calc p2_161.t = p2_161 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_162_contains : p2_162.Contains (quadraturePoint 2 162) := by
  have ht : p2_162.t.Contains (quadraturePoint 2 162) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨162,by decide⟩).scale 1 12) = p2_162.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨162,by decide⟩
  have he : PointBox.calc p2_162.t = p2_162 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_163_contains : p2_163.Contains (quadraturePoint 2 163) := by
  have ht : p2_163.t.Contains (quadraturePoint 2 163) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨163,by decide⟩).scale 1 12) = p2_163.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨163,by decide⟩
  have he : PointBox.calc p2_163.t = p2_163 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_164_contains : p2_164.Contains (quadraturePoint 2 164) := by
  have ht : p2_164.t.Contains (quadraturePoint 2 164) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨164,by decide⟩).scale 1 12) = p2_164.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨164,by decide⟩
  have he : PointBox.calc p2_164.t = p2_164 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_165_contains : p2_165.Contains (quadraturePoint 2 165) := by
  have ht : p2_165.t.Contains (quadraturePoint 2 165) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨165,by decide⟩).scale 1 12) = p2_165.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨165,by decide⟩
  have he : PointBox.calc p2_165.t = p2_165 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_166_contains : p2_166.Contains (quadraturePoint 2 166) := by
  have ht : p2_166.t.Contains (quadraturePoint 2 166) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨166,by decide⟩).scale 1 12) = p2_166.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨166,by decide⟩
  have he : PointBox.calc p2_166.t = p2_166 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_167_contains : p2_167.Contains (quadraturePoint 2 167) := by
  have ht : p2_167.t.Contains (quadraturePoint 2 167) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨167,by decide⟩).scale 1 12) = p2_167.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨167,by decide⟩
  have he : PointBox.calc p2_167.t = p2_167 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_168_contains : p2_168.Contains (quadraturePoint 2 168) := by
  have ht : p2_168.t.Contains (quadraturePoint 2 168) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨168,by decide⟩).scale 1 12) = p2_168.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨168,by decide⟩
  have he : PointBox.calc p2_168.t = p2_168 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_169_contains : p2_169.Contains (quadraturePoint 2 169) := by
  have ht : p2_169.t.Contains (quadraturePoint 2 169) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨169,by decide⟩).scale 1 12) = p2_169.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨169,by decide⟩
  have he : PointBox.calc p2_169.t = p2_169 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_170_contains : p2_170.Contains (quadraturePoint 2 170) := by
  have ht : p2_170.t.Contains (quadraturePoint 2 170) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨170,by decide⟩).scale 1 12) = p2_170.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨170,by decide⟩
  have he : PointBox.calc p2_170.t = p2_170 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_171_contains : p2_171.Contains (quadraturePoint 2 171) := by
  have ht : p2_171.t.Contains (quadraturePoint 2 171) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨171,by decide⟩).scale 1 12) = p2_171.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨171,by decide⟩
  have he : PointBox.calc p2_171.t = p2_171 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_172_contains : p2_172.Contains (quadraturePoint 2 172) := by
  have ht : p2_172.t.Contains (quadraturePoint 2 172) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨172,by decide⟩).scale 1 12) = p2_172.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨172,by decide⟩
  have he : PointBox.calc p2_172.t = p2_172 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_173_contains : p2_173.Contains (quadraturePoint 2 173) := by
  have ht : p2_173.t.Contains (quadraturePoint 2 173) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨173,by decide⟩).scale 1 12) = p2_173.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨173,by decide⟩
  have he : PointBox.calc p2_173.t = p2_173 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_174_contains : p2_174.Contains (quadraturePoint 2 174) := by
  have ht : p2_174.t.Contains (quadraturePoint 2 174) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨174,by decide⟩).scale 1 12) = p2_174.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨174,by decide⟩
  have he : PointBox.calc p2_174.t = p2_174 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_175_contains : p2_175.Contains (quadraturePoint 2 175) := by
  have ht : p2_175.t.Contains (quadraturePoint 2 175) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨175,by decide⟩).scale 1 12) = p2_175.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨175,by decide⟩
  have he : PointBox.calc p2_175.t = p2_175 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row2_10_contains_g_oai (k : Fin 16) : (row2_10 k).Contains (quadraturePoint 2 (160+k.val)) := by
  fin_cases k
  · exact p2_160_contains
  · exact p2_161_contains
  · exact p2_162_contains
  · exact p2_163_contains
  · exact p2_164_contains
  · exact p2_165_contains
  · exact p2_166_contains
  · exact p2_167_contains
  · exact p2_168_contains
  · exact p2_169_contains
  · exact p2_170_contains
  · exact p2_171_contains
  · exact p2_172_contains
  · exact p2_173_contains
  · exact p2_174_contains
  · exact p2_175_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row2_10_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row2_10_contains_g_oai
