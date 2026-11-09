-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:07.66721+00:00
-- url     : https://prove2.me/submissions/cd6c2679-5baf-407b-8e97-c45344f7c33a

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

lemma p1_160_contains : p1_160.Contains (quadraturePoint 1 160) := by
  have ht : p1_160.t.Contains (quadraturePoint 1 160) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨160,by decide⟩).scale 1 12) = p1_160.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨160,by decide⟩
  have he : PointBox.calc p1_160.t = p1_160 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_161_contains : p1_161.Contains (quadraturePoint 1 161) := by
  have ht : p1_161.t.Contains (quadraturePoint 1 161) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨161,by decide⟩).scale 1 12) = p1_161.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨161,by decide⟩
  have he : PointBox.calc p1_161.t = p1_161 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_162_contains : p1_162.Contains (quadraturePoint 1 162) := by
  have ht : p1_162.t.Contains (quadraturePoint 1 162) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨162,by decide⟩).scale 1 12) = p1_162.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨162,by decide⟩
  have he : PointBox.calc p1_162.t = p1_162 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_163_contains : p1_163.Contains (quadraturePoint 1 163) := by
  have ht : p1_163.t.Contains (quadraturePoint 1 163) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨163,by decide⟩).scale 1 12) = p1_163.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨163,by decide⟩
  have he : PointBox.calc p1_163.t = p1_163 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_164_contains : p1_164.Contains (quadraturePoint 1 164) := by
  have ht : p1_164.t.Contains (quadraturePoint 1 164) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨164,by decide⟩).scale 1 12) = p1_164.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨164,by decide⟩
  have he : PointBox.calc p1_164.t = p1_164 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_165_contains : p1_165.Contains (quadraturePoint 1 165) := by
  have ht : p1_165.t.Contains (quadraturePoint 1 165) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨165,by decide⟩).scale 1 12) = p1_165.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨165,by decide⟩
  have he : PointBox.calc p1_165.t = p1_165 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_166_contains : p1_166.Contains (quadraturePoint 1 166) := by
  have ht : p1_166.t.Contains (quadraturePoint 1 166) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨166,by decide⟩).scale 1 12) = p1_166.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨166,by decide⟩
  have he : PointBox.calc p1_166.t = p1_166 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_167_contains : p1_167.Contains (quadraturePoint 1 167) := by
  have ht : p1_167.t.Contains (quadraturePoint 1 167) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨167,by decide⟩).scale 1 12) = p1_167.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨167,by decide⟩
  have he : PointBox.calc p1_167.t = p1_167 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_168_contains : p1_168.Contains (quadraturePoint 1 168) := by
  have ht : p1_168.t.Contains (quadraturePoint 1 168) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨168,by decide⟩).scale 1 12) = p1_168.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨168,by decide⟩
  have he : PointBox.calc p1_168.t = p1_168 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_169_contains : p1_169.Contains (quadraturePoint 1 169) := by
  have ht : p1_169.t.Contains (quadraturePoint 1 169) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨169,by decide⟩).scale 1 12) = p1_169.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨169,by decide⟩
  have he : PointBox.calc p1_169.t = p1_169 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_170_contains : p1_170.Contains (quadraturePoint 1 170) := by
  have ht : p1_170.t.Contains (quadraturePoint 1 170) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨170,by decide⟩).scale 1 12) = p1_170.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨170,by decide⟩
  have he : PointBox.calc p1_170.t = p1_170 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_171_contains : p1_171.Contains (quadraturePoint 1 171) := by
  have ht : p1_171.t.Contains (quadraturePoint 1 171) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨171,by decide⟩).scale 1 12) = p1_171.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨171,by decide⟩
  have he : PointBox.calc p1_171.t = p1_171 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_172_contains : p1_172.Contains (quadraturePoint 1 172) := by
  have ht : p1_172.t.Contains (quadraturePoint 1 172) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨172,by decide⟩).scale 1 12) = p1_172.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨172,by decide⟩
  have he : PointBox.calc p1_172.t = p1_172 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_173_contains : p1_173.Contains (quadraturePoint 1 173) := by
  have ht : p1_173.t.Contains (quadraturePoint 1 173) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨173,by decide⟩).scale 1 12) = p1_173.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨173,by decide⟩
  have he : PointBox.calc p1_173.t = p1_173 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_174_contains : p1_174.Contains (quadraturePoint 1 174) := by
  have ht : p1_174.t.Contains (quadraturePoint 1 174) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨174,by decide⟩).scale 1 12) = p1_174.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨174,by decide⟩
  have he : PointBox.calc p1_174.t = p1_174 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_175_contains : p1_175.Contains (quadraturePoint 1 175) := by
  have ht : p1_175.t.Contains (quadraturePoint 1 175) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨175,by decide⟩).scale 1 12) = p1_175.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨175,by decide⟩
  have he : PointBox.calc p1_175.t = p1_175 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_10_contains_g_oai (k : Fin 16) : (row1_10 k).Contains (quadraturePoint 1 (160+k.val)) := by
  fin_cases k
  · exact p1_160_contains
  · exact p1_161_contains
  · exact p1_162_contains
  · exact p1_163_contains
  · exact p1_164_contains
  · exact p1_165_contains
  · exact p1_166_contains
  · exact p1_167_contains
  · exact p1_168_contains
  · exact p1_169_contains
  · exact p1_170_contains
  · exact p1_171_contains
  · exact p1_172_contains
  · exact p1_173_contains
  · exact p1_174_contains
  · exact p1_175_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_10_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_10_contains_g_oai
