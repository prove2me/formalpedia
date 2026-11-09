-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_15_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:16.80022+00:00
-- url     : https://prove2.me/submissions/45dcabd7-bc10-4adc-85f7-cdb1eef5bc99

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

lemma p1_240_contains : p1_240.Contains (quadraturePoint 1 240) := by
  have ht : p1_240.t.Contains (quadraturePoint 1 240) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨240,by decide⟩).scale 1 12) = p1_240.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨240,by decide⟩
  have he : PointBox.calc p1_240.t = p1_240 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_241_contains : p1_241.Contains (quadraturePoint 1 241) := by
  have ht : p1_241.t.Contains (quadraturePoint 1 241) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨241,by decide⟩).scale 1 12) = p1_241.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨241,by decide⟩
  have he : PointBox.calc p1_241.t = p1_241 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_242_contains : p1_242.Contains (quadraturePoint 1 242) := by
  have ht : p1_242.t.Contains (quadraturePoint 1 242) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨242,by decide⟩).scale 1 12) = p1_242.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨242,by decide⟩
  have he : PointBox.calc p1_242.t = p1_242 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_243_contains : p1_243.Contains (quadraturePoint 1 243) := by
  have ht : p1_243.t.Contains (quadraturePoint 1 243) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨243,by decide⟩).scale 1 12) = p1_243.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨243,by decide⟩
  have he : PointBox.calc p1_243.t = p1_243 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_244_contains : p1_244.Contains (quadraturePoint 1 244) := by
  have ht : p1_244.t.Contains (quadraturePoint 1 244) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨244,by decide⟩).scale 1 12) = p1_244.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨244,by decide⟩
  have he : PointBox.calc p1_244.t = p1_244 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_245_contains : p1_245.Contains (quadraturePoint 1 245) := by
  have ht : p1_245.t.Contains (quadraturePoint 1 245) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨245,by decide⟩).scale 1 12) = p1_245.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨245,by decide⟩
  have he : PointBox.calc p1_245.t = p1_245 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_246_contains : p1_246.Contains (quadraturePoint 1 246) := by
  have ht : p1_246.t.Contains (quadraturePoint 1 246) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨246,by decide⟩).scale 1 12) = p1_246.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨246,by decide⟩
  have he : PointBox.calc p1_246.t = p1_246 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_247_contains : p1_247.Contains (quadraturePoint 1 247) := by
  have ht : p1_247.t.Contains (quadraturePoint 1 247) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨247,by decide⟩).scale 1 12) = p1_247.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨247,by decide⟩
  have he : PointBox.calc p1_247.t = p1_247 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_248_contains : p1_248.Contains (quadraturePoint 1 248) := by
  have ht : p1_248.t.Contains (quadraturePoint 1 248) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨248,by decide⟩).scale 1 12) = p1_248.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨248,by decide⟩
  have he : PointBox.calc p1_248.t = p1_248 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_249_contains : p1_249.Contains (quadraturePoint 1 249) := by
  have ht : p1_249.t.Contains (quadraturePoint 1 249) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨249,by decide⟩).scale 1 12) = p1_249.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨249,by decide⟩
  have he : PointBox.calc p1_249.t = p1_249 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_250_contains : p1_250.Contains (quadraturePoint 1 250) := by
  have ht : p1_250.t.Contains (quadraturePoint 1 250) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨250,by decide⟩).scale 1 12) = p1_250.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨250,by decide⟩
  have he : PointBox.calc p1_250.t = p1_250 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_251_contains : p1_251.Contains (quadraturePoint 1 251) := by
  have ht : p1_251.t.Contains (quadraturePoint 1 251) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨251,by decide⟩).scale 1 12) = p1_251.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨251,by decide⟩
  have he : PointBox.calc p1_251.t = p1_251 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_252_contains : p1_252.Contains (quadraturePoint 1 252) := by
  have ht : p1_252.t.Contains (quadraturePoint 1 252) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨252,by decide⟩).scale 1 12) = p1_252.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨252,by decide⟩
  have he : PointBox.calc p1_252.t = p1_252 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_253_contains : p1_253.Contains (quadraturePoint 1 253) := by
  have ht : p1_253.t.Contains (quadraturePoint 1 253) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨253,by decide⟩).scale 1 12) = p1_253.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨253,by decide⟩
  have he : PointBox.calc p1_253.t = p1_253 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_254_contains : p1_254.Contains (quadraturePoint 1 254) := by
  have ht : p1_254.t.Contains (quadraturePoint 1 254) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨254,by decide⟩).scale 1 12) = p1_254.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨254,by decide⟩
  have he : PointBox.calc p1_254.t = p1_254 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_255_contains : p1_255.Contains (quadraturePoint 1 255) := by
  have ht : p1_255.t.Contains (quadraturePoint 1 255) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨255,by decide⟩).scale 1 12) = p1_255.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨255,by decide⟩
  have he : PointBox.calc p1_255.t = p1_255 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_15_contains_g_oai (k : Fin 16) : (row1_15 k).Contains (quadraturePoint 1 (240+k.val)) := by
  fin_cases k
  · exact p1_240_contains
  · exact p1_241_contains
  · exact p1_242_contains
  · exact p1_243_contains
  · exact p1_244_contains
  · exact p1_245_contains
  · exact p1_246_contains
  · exact p1_247_contains
  · exact p1_248_contains
  · exact p1_249_contains
  · exact p1_250_contains
  · exact p1_251_contains
  · exact p1_252_contains
  · exact p1_253_contains
  · exact p1_254_contains
  · exact p1_255_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_15_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_15_contains_g_oai
