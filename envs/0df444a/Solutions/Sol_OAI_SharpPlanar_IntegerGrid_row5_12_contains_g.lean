-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_12_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:09.194129+00:00
-- url     : https://prove2.me/submissions/a4b2495b-f44f-4963-bbc9-7e9c51810606

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

lemma p5_192_contains : p5_192.Contains (quadraturePoint 5 192) := by
  have ht : p5_192.t.Contains (quadraturePoint 5 192) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨192,by decide⟩).scale 1 12) = p5_192.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨192,by decide⟩
  have he : PointBox.calc p5_192.t = p5_192 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_193_contains : p5_193.Contains (quadraturePoint 5 193) := by
  have ht : p5_193.t.Contains (quadraturePoint 5 193) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨193,by decide⟩).scale 1 12) = p5_193.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨193,by decide⟩
  have he : PointBox.calc p5_193.t = p5_193 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_194_contains : p5_194.Contains (quadraturePoint 5 194) := by
  have ht : p5_194.t.Contains (quadraturePoint 5 194) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨194,by decide⟩).scale 1 12) = p5_194.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨194,by decide⟩
  have he : PointBox.calc p5_194.t = p5_194 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_195_contains : p5_195.Contains (quadraturePoint 5 195) := by
  have ht : p5_195.t.Contains (quadraturePoint 5 195) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨195,by decide⟩).scale 1 12) = p5_195.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨195,by decide⟩
  have he : PointBox.calc p5_195.t = p5_195 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_196_contains : p5_196.Contains (quadraturePoint 5 196) := by
  have ht : p5_196.t.Contains (quadraturePoint 5 196) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨196,by decide⟩).scale 1 12) = p5_196.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨196,by decide⟩
  have he : PointBox.calc p5_196.t = p5_196 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_197_contains : p5_197.Contains (quadraturePoint 5 197) := by
  have ht : p5_197.t.Contains (quadraturePoint 5 197) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨197,by decide⟩).scale 1 12) = p5_197.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨197,by decide⟩
  have he : PointBox.calc p5_197.t = p5_197 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_198_contains : p5_198.Contains (quadraturePoint 5 198) := by
  have ht : p5_198.t.Contains (quadraturePoint 5 198) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨198,by decide⟩).scale 1 12) = p5_198.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨198,by decide⟩
  have he : PointBox.calc p5_198.t = p5_198 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_199_contains : p5_199.Contains (quadraturePoint 5 199) := by
  have ht : p5_199.t.Contains (quadraturePoint 5 199) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨199,by decide⟩).scale 1 12) = p5_199.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨199,by decide⟩
  have he : PointBox.calc p5_199.t = p5_199 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_200_contains : p5_200.Contains (quadraturePoint 5 200) := by
  have ht : p5_200.t.Contains (quadraturePoint 5 200) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨200,by decide⟩).scale 1 12) = p5_200.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨200,by decide⟩
  have he : PointBox.calc p5_200.t = p5_200 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_201_contains : p5_201.Contains (quadraturePoint 5 201) := by
  have ht : p5_201.t.Contains (quadraturePoint 5 201) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨201,by decide⟩).scale 1 12) = p5_201.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨201,by decide⟩
  have he : PointBox.calc p5_201.t = p5_201 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_202_contains : p5_202.Contains (quadraturePoint 5 202) := by
  have ht : p5_202.t.Contains (quadraturePoint 5 202) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨202,by decide⟩).scale 1 12) = p5_202.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨202,by decide⟩
  have he : PointBox.calc p5_202.t = p5_202 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_203_contains : p5_203.Contains (quadraturePoint 5 203) := by
  have ht : p5_203.t.Contains (quadraturePoint 5 203) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨203,by decide⟩).scale 1 12) = p5_203.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨203,by decide⟩
  have he : PointBox.calc p5_203.t = p5_203 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_204_contains : p5_204.Contains (quadraturePoint 5 204) := by
  have ht : p5_204.t.Contains (quadraturePoint 5 204) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨204,by decide⟩).scale 1 12) = p5_204.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨204,by decide⟩
  have he : PointBox.calc p5_204.t = p5_204 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_205_contains : p5_205.Contains (quadraturePoint 5 205) := by
  have ht : p5_205.t.Contains (quadraturePoint 5 205) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨205,by decide⟩).scale 1 12) = p5_205.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨205,by decide⟩
  have he : PointBox.calc p5_205.t = p5_205 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_206_contains : p5_206.Contains (quadraturePoint 5 206) := by
  have ht : p5_206.t.Contains (quadraturePoint 5 206) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨206,by decide⟩).scale 1 12) = p5_206.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨206,by decide⟩
  have he : PointBox.calc p5_206.t = p5_206 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_207_contains : p5_207.Contains (quadraturePoint 5 207) := by
  have ht : p5_207.t.Contains (quadraturePoint 5 207) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨207,by decide⟩).scale 1 12) = p5_207.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨207,by decide⟩
  have he : PointBox.calc p5_207.t = p5_207 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_12_contains_g_oai (k : Fin 16) : (row5_12 k).Contains (quadraturePoint 5 (192+k.val)) := by
  fin_cases k
  · exact p5_192_contains
  · exact p5_193_contains
  · exact p5_194_contains
  · exact p5_195_contains
  · exact p5_196_contains
  · exact p5_197_contains
  · exact p5_198_contains
  · exact p5_199_contains
  · exact p5_200_contains
  · exact p5_201_contains
  · exact p5_202_contains
  · exact p5_203_contains
  · exact p5_204_contains
  · exact p5_205_contains
  · exact p5_206_contains
  · exact p5_207_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_12_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_12_contains_g_oai
