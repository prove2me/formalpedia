-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row2_12_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:39.122761+00:00
-- url     : https://prove2.me/submissions/6450ed44-a69d-4b53-88f3-97888ef06df2

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

lemma p2_192_contains : p2_192.Contains (quadraturePoint 2 192) := by
  have ht : p2_192.t.Contains (quadraturePoint 2 192) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨192,by decide⟩).scale 1 12) = p2_192.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨192,by decide⟩
  have he : PointBox.calc p2_192.t = p2_192 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_193_contains : p2_193.Contains (quadraturePoint 2 193) := by
  have ht : p2_193.t.Contains (quadraturePoint 2 193) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨193,by decide⟩).scale 1 12) = p2_193.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨193,by decide⟩
  have he : PointBox.calc p2_193.t = p2_193 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_194_contains : p2_194.Contains (quadraturePoint 2 194) := by
  have ht : p2_194.t.Contains (quadraturePoint 2 194) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨194,by decide⟩).scale 1 12) = p2_194.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨194,by decide⟩
  have he : PointBox.calc p2_194.t = p2_194 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_195_contains : p2_195.Contains (quadraturePoint 2 195) := by
  have ht : p2_195.t.Contains (quadraturePoint 2 195) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨195,by decide⟩).scale 1 12) = p2_195.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨195,by decide⟩
  have he : PointBox.calc p2_195.t = p2_195 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_196_contains : p2_196.Contains (quadraturePoint 2 196) := by
  have ht : p2_196.t.Contains (quadraturePoint 2 196) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨196,by decide⟩).scale 1 12) = p2_196.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨196,by decide⟩
  have he : PointBox.calc p2_196.t = p2_196 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_197_contains : p2_197.Contains (quadraturePoint 2 197) := by
  have ht : p2_197.t.Contains (quadraturePoint 2 197) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨197,by decide⟩).scale 1 12) = p2_197.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨197,by decide⟩
  have he : PointBox.calc p2_197.t = p2_197 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_198_contains : p2_198.Contains (quadraturePoint 2 198) := by
  have ht : p2_198.t.Contains (quadraturePoint 2 198) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨198,by decide⟩).scale 1 12) = p2_198.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨198,by decide⟩
  have he : PointBox.calc p2_198.t = p2_198 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_199_contains : p2_199.Contains (quadraturePoint 2 199) := by
  have ht : p2_199.t.Contains (quadraturePoint 2 199) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨199,by decide⟩).scale 1 12) = p2_199.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨199,by decide⟩
  have he : PointBox.calc p2_199.t = p2_199 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_200_contains : p2_200.Contains (quadraturePoint 2 200) := by
  have ht : p2_200.t.Contains (quadraturePoint 2 200) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨200,by decide⟩).scale 1 12) = p2_200.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨200,by decide⟩
  have he : PointBox.calc p2_200.t = p2_200 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_201_contains : p2_201.Contains (quadraturePoint 2 201) := by
  have ht : p2_201.t.Contains (quadraturePoint 2 201) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨201,by decide⟩).scale 1 12) = p2_201.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨201,by decide⟩
  have he : PointBox.calc p2_201.t = p2_201 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_202_contains : p2_202.Contains (quadraturePoint 2 202) := by
  have ht : p2_202.t.Contains (quadraturePoint 2 202) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨202,by decide⟩).scale 1 12) = p2_202.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨202,by decide⟩
  have he : PointBox.calc p2_202.t = p2_202 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_203_contains : p2_203.Contains (quadraturePoint 2 203) := by
  have ht : p2_203.t.Contains (quadraturePoint 2 203) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨203,by decide⟩).scale 1 12) = p2_203.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨203,by decide⟩
  have he : PointBox.calc p2_203.t = p2_203 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_204_contains : p2_204.Contains (quadraturePoint 2 204) := by
  have ht : p2_204.t.Contains (quadraturePoint 2 204) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨204,by decide⟩).scale 1 12) = p2_204.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨204,by decide⟩
  have he : PointBox.calc p2_204.t = p2_204 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_205_contains : p2_205.Contains (quadraturePoint 2 205) := by
  have ht : p2_205.t.Contains (quadraturePoint 2 205) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨205,by decide⟩).scale 1 12) = p2_205.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨205,by decide⟩
  have he : PointBox.calc p2_205.t = p2_205 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_206_contains : p2_206.Contains (quadraturePoint 2 206) := by
  have ht : p2_206.t.Contains (quadraturePoint 2 206) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨206,by decide⟩).scale 1 12) = p2_206.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨206,by decide⟩
  have he : PointBox.calc p2_206.t = p2_206 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_207_contains : p2_207.Contains (quadraturePoint 2 207) := by
  have ht : p2_207.t.Contains (quadraturePoint 2 207) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨207,by decide⟩).scale 1 12) = p2_207.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨207,by decide⟩
  have he : PointBox.calc p2_207.t = p2_207 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row2_12_contains_g_oai (k : Fin 16) : (row2_12 k).Contains (quadraturePoint 2 (192+k.val)) := by
  fin_cases k
  · exact p2_192_contains
  · exact p2_193_contains
  · exact p2_194_contains
  · exact p2_195_contains
  · exact p2_196_contains
  · exact p2_197_contains
  · exact p2_198_contains
  · exact p2_199_contains
  · exact p2_200_contains
  · exact p2_201_contains
  · exact p2_202_contains
  · exact p2_203_contains
  · exact p2_204_contains
  · exact p2_205_contains
  · exact p2_206_contains
  · exact p2_207_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row2_12_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row2_12_contains_g_oai
