-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row4_12_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:22.439201+00:00
-- url     : https://prove2.me/submissions/ca1abaa3-6f13-4505-b059-7b3d811bbd1c

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

lemma p4_192_contains : p4_192.Contains (quadraturePoint 4 192) := by
  have ht : p4_192.t.Contains (quadraturePoint 4 192) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨192,by decide⟩).scale 1 12) = p4_192.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨192,by decide⟩
  have he : PointBox.calc p4_192.t = p4_192 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_193_contains : p4_193.Contains (quadraturePoint 4 193) := by
  have ht : p4_193.t.Contains (quadraturePoint 4 193) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨193,by decide⟩).scale 1 12) = p4_193.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨193,by decide⟩
  have he : PointBox.calc p4_193.t = p4_193 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_194_contains : p4_194.Contains (quadraturePoint 4 194) := by
  have ht : p4_194.t.Contains (quadraturePoint 4 194) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨194,by decide⟩).scale 1 12) = p4_194.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨194,by decide⟩
  have he : PointBox.calc p4_194.t = p4_194 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_195_contains : p4_195.Contains (quadraturePoint 4 195) := by
  have ht : p4_195.t.Contains (quadraturePoint 4 195) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨195,by decide⟩).scale 1 12) = p4_195.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨195,by decide⟩
  have he : PointBox.calc p4_195.t = p4_195 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_196_contains : p4_196.Contains (quadraturePoint 4 196) := by
  have ht : p4_196.t.Contains (quadraturePoint 4 196) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨196,by decide⟩).scale 1 12) = p4_196.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨196,by decide⟩
  have he : PointBox.calc p4_196.t = p4_196 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_197_contains : p4_197.Contains (quadraturePoint 4 197) := by
  have ht : p4_197.t.Contains (quadraturePoint 4 197) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨197,by decide⟩).scale 1 12) = p4_197.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨197,by decide⟩
  have he : PointBox.calc p4_197.t = p4_197 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_198_contains : p4_198.Contains (quadraturePoint 4 198) := by
  have ht : p4_198.t.Contains (quadraturePoint 4 198) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨198,by decide⟩).scale 1 12) = p4_198.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨198,by decide⟩
  have he : PointBox.calc p4_198.t = p4_198 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_199_contains : p4_199.Contains (quadraturePoint 4 199) := by
  have ht : p4_199.t.Contains (quadraturePoint 4 199) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨199,by decide⟩).scale 1 12) = p4_199.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨199,by decide⟩
  have he : PointBox.calc p4_199.t = p4_199 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_200_contains : p4_200.Contains (quadraturePoint 4 200) := by
  have ht : p4_200.t.Contains (quadraturePoint 4 200) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨200,by decide⟩).scale 1 12) = p4_200.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨200,by decide⟩
  have he : PointBox.calc p4_200.t = p4_200 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_201_contains : p4_201.Contains (quadraturePoint 4 201) := by
  have ht : p4_201.t.Contains (quadraturePoint 4 201) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨201,by decide⟩).scale 1 12) = p4_201.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨201,by decide⟩
  have he : PointBox.calc p4_201.t = p4_201 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_202_contains : p4_202.Contains (quadraturePoint 4 202) := by
  have ht : p4_202.t.Contains (quadraturePoint 4 202) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨202,by decide⟩).scale 1 12) = p4_202.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨202,by decide⟩
  have he : PointBox.calc p4_202.t = p4_202 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_203_contains : p4_203.Contains (quadraturePoint 4 203) := by
  have ht : p4_203.t.Contains (quadraturePoint 4 203) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨203,by decide⟩).scale 1 12) = p4_203.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨203,by decide⟩
  have he : PointBox.calc p4_203.t = p4_203 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_204_contains : p4_204.Contains (quadraturePoint 4 204) := by
  have ht : p4_204.t.Contains (quadraturePoint 4 204) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨204,by decide⟩).scale 1 12) = p4_204.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨204,by decide⟩
  have he : PointBox.calc p4_204.t = p4_204 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_205_contains : p4_205.Contains (quadraturePoint 4 205) := by
  have ht : p4_205.t.Contains (quadraturePoint 4 205) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨205,by decide⟩).scale 1 12) = p4_205.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨205,by decide⟩
  have he : PointBox.calc p4_205.t = p4_205 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_206_contains : p4_206.Contains (quadraturePoint 4 206) := by
  have ht : p4_206.t.Contains (quadraturePoint 4 206) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨206,by decide⟩).scale 1 12) = p4_206.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨206,by decide⟩
  have he : PointBox.calc p4_206.t = p4_206 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_207_contains : p4_207.Contains (quadraturePoint 4 207) := by
  have ht : p4_207.t.Contains (quadraturePoint 4 207) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨207,by decide⟩).scale 1 12) = p4_207.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨207,by decide⟩
  have he : PointBox.calc p4_207.t = p4_207 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row4_12_contains_g_oai (k : Fin 16) : (row4_12 k).Contains (quadraturePoint 4 (192+k.val)) := by
  fin_cases k
  · exact p4_192_contains
  · exact p4_193_contains
  · exact p4_194_contains
  · exact p4_195_contains
  · exact p4_196_contains
  · exact p4_197_contains
  · exact p4_198_contains
  · exact p4_199_contains
  · exact p4_200_contains
  · exact p4_201_contains
  · exact p4_202_contains
  · exact p4_203_contains
  · exact p4_204_contains
  · exact p4_205_contains
  · exact p4_206_contains
  · exact p4_207_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row4_12_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row4_12_contains_g_oai
