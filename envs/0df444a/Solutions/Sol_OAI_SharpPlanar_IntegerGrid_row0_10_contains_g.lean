-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:55.093412+00:00
-- url     : https://prove2.me/submissions/bea18bb6-7d08-4007-8347-4f7c658dab0c

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

lemma p0_160_contains : p0_160.Contains (quadraturePoint 0 160) := by
  have ht : p0_160.t.Contains (quadraturePoint 0 160) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨160,by decide⟩).scale 1 12) = p0_160.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨160,by decide⟩
  have he : PointBox.calc p0_160.t = p0_160 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_161_contains : p0_161.Contains (quadraturePoint 0 161) := by
  have ht : p0_161.t.Contains (quadraturePoint 0 161) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨161,by decide⟩).scale 1 12) = p0_161.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨161,by decide⟩
  have he : PointBox.calc p0_161.t = p0_161 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_162_contains : p0_162.Contains (quadraturePoint 0 162) := by
  have ht : p0_162.t.Contains (quadraturePoint 0 162) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨162,by decide⟩).scale 1 12) = p0_162.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨162,by decide⟩
  have he : PointBox.calc p0_162.t = p0_162 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_163_contains : p0_163.Contains (quadraturePoint 0 163) := by
  have ht : p0_163.t.Contains (quadraturePoint 0 163) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨163,by decide⟩).scale 1 12) = p0_163.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨163,by decide⟩
  have he : PointBox.calc p0_163.t = p0_163 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_164_contains : p0_164.Contains (quadraturePoint 0 164) := by
  have ht : p0_164.t.Contains (quadraturePoint 0 164) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨164,by decide⟩).scale 1 12) = p0_164.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨164,by decide⟩
  have he : PointBox.calc p0_164.t = p0_164 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_165_contains : p0_165.Contains (quadraturePoint 0 165) := by
  have ht : p0_165.t.Contains (quadraturePoint 0 165) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨165,by decide⟩).scale 1 12) = p0_165.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨165,by decide⟩
  have he : PointBox.calc p0_165.t = p0_165 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_166_contains : p0_166.Contains (quadraturePoint 0 166) := by
  have ht : p0_166.t.Contains (quadraturePoint 0 166) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨166,by decide⟩).scale 1 12) = p0_166.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨166,by decide⟩
  have he : PointBox.calc p0_166.t = p0_166 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_167_contains : p0_167.Contains (quadraturePoint 0 167) := by
  have ht : p0_167.t.Contains (quadraturePoint 0 167) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨167,by decide⟩).scale 1 12) = p0_167.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨167,by decide⟩
  have he : PointBox.calc p0_167.t = p0_167 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_168_contains : p0_168.Contains (quadraturePoint 0 168) := by
  have ht : p0_168.t.Contains (quadraturePoint 0 168) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨168,by decide⟩).scale 1 12) = p0_168.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨168,by decide⟩
  have he : PointBox.calc p0_168.t = p0_168 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_169_contains : p0_169.Contains (quadraturePoint 0 169) := by
  have ht : p0_169.t.Contains (quadraturePoint 0 169) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨169,by decide⟩).scale 1 12) = p0_169.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨169,by decide⟩
  have he : PointBox.calc p0_169.t = p0_169 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_170_contains : p0_170.Contains (quadraturePoint 0 170) := by
  have ht : p0_170.t.Contains (quadraturePoint 0 170) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨170,by decide⟩).scale 1 12) = p0_170.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨170,by decide⟩
  have he : PointBox.calc p0_170.t = p0_170 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_171_contains : p0_171.Contains (quadraturePoint 0 171) := by
  have ht : p0_171.t.Contains (quadraturePoint 0 171) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨171,by decide⟩).scale 1 12) = p0_171.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨171,by decide⟩
  have he : PointBox.calc p0_171.t = p0_171 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_172_contains : p0_172.Contains (quadraturePoint 0 172) := by
  have ht : p0_172.t.Contains (quadraturePoint 0 172) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨172,by decide⟩).scale 1 12) = p0_172.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨172,by decide⟩
  have he : PointBox.calc p0_172.t = p0_172 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_173_contains : p0_173.Contains (quadraturePoint 0 173) := by
  have ht : p0_173.t.Contains (quadraturePoint 0 173) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨173,by decide⟩).scale 1 12) = p0_173.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨173,by decide⟩
  have he : PointBox.calc p0_173.t = p0_173 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_174_contains : p0_174.Contains (quadraturePoint 0 174) := by
  have ht : p0_174.t.Contains (quadraturePoint 0 174) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨174,by decide⟩).scale 1 12) = p0_174.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨174,by decide⟩
  have he : PointBox.calc p0_174.t = p0_174 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_175_contains : p0_175.Contains (quadraturePoint 0 175) := by
  have ht : p0_175.t.Contains (quadraturePoint 0 175) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨175,by decide⟩).scale 1 12) = p0_175.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨175,by decide⟩
  have he : PointBox.calc p0_175.t = p0_175 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_10_contains_g_oai (k : Fin 16) : (row0_10 k).Contains (quadraturePoint 0 (160+k.val)) := by
  fin_cases k
  · exact p0_160_contains
  · exact p0_161_contains
  · exact p0_162_contains
  · exact p0_163_contains
  · exact p0_164_contains
  · exact p0_165_contains
  · exact p0_166_contains
  · exact p0_167_contains
  · exact p0_168_contains
  · exact p0_169_contains
  · exact p0_170_contains
  · exact p0_171_contains
  · exact p0_172_contains
  · exact p0_173_contains
  · exact p0_174_contains
  · exact p0_175_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_10_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_10_contains_g_oai
