-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_15_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:13.187809+00:00
-- url     : https://prove2.me/submissions/b68cdc51-75ae-4ed7-801c-2cf54e5443ed

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

lemma p5_240_contains : p5_240.Contains (quadraturePoint 5 240) := by
  have ht : p5_240.t.Contains (quadraturePoint 5 240) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨240,by decide⟩).scale 1 12) = p5_240.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨240,by decide⟩
  have he : PointBox.calc p5_240.t = p5_240 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_241_contains : p5_241.Contains (quadraturePoint 5 241) := by
  have ht : p5_241.t.Contains (quadraturePoint 5 241) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨241,by decide⟩).scale 1 12) = p5_241.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨241,by decide⟩
  have he : PointBox.calc p5_241.t = p5_241 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_242_contains : p5_242.Contains (quadraturePoint 5 242) := by
  have ht : p5_242.t.Contains (quadraturePoint 5 242) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨242,by decide⟩).scale 1 12) = p5_242.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨242,by decide⟩
  have he : PointBox.calc p5_242.t = p5_242 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_243_contains : p5_243.Contains (quadraturePoint 5 243) := by
  have ht : p5_243.t.Contains (quadraturePoint 5 243) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨243,by decide⟩).scale 1 12) = p5_243.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨243,by decide⟩
  have he : PointBox.calc p5_243.t = p5_243 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_244_contains : p5_244.Contains (quadraturePoint 5 244) := by
  have ht : p5_244.t.Contains (quadraturePoint 5 244) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨244,by decide⟩).scale 1 12) = p5_244.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨244,by decide⟩
  have he : PointBox.calc p5_244.t = p5_244 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_245_contains : p5_245.Contains (quadraturePoint 5 245) := by
  have ht : p5_245.t.Contains (quadraturePoint 5 245) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨245,by decide⟩).scale 1 12) = p5_245.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨245,by decide⟩
  have he : PointBox.calc p5_245.t = p5_245 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_246_contains : p5_246.Contains (quadraturePoint 5 246) := by
  have ht : p5_246.t.Contains (quadraturePoint 5 246) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨246,by decide⟩).scale 1 12) = p5_246.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨246,by decide⟩
  have he : PointBox.calc p5_246.t = p5_246 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_247_contains : p5_247.Contains (quadraturePoint 5 247) := by
  have ht : p5_247.t.Contains (quadraturePoint 5 247) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨247,by decide⟩).scale 1 12) = p5_247.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨247,by decide⟩
  have he : PointBox.calc p5_247.t = p5_247 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_248_contains : p5_248.Contains (quadraturePoint 5 248) := by
  have ht : p5_248.t.Contains (quadraturePoint 5 248) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨248,by decide⟩).scale 1 12) = p5_248.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨248,by decide⟩
  have he : PointBox.calc p5_248.t = p5_248 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_249_contains : p5_249.Contains (quadraturePoint 5 249) := by
  have ht : p5_249.t.Contains (quadraturePoint 5 249) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨249,by decide⟩).scale 1 12) = p5_249.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨249,by decide⟩
  have he : PointBox.calc p5_249.t = p5_249 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_250_contains : p5_250.Contains (quadraturePoint 5 250) := by
  have ht : p5_250.t.Contains (quadraturePoint 5 250) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨250,by decide⟩).scale 1 12) = p5_250.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨250,by decide⟩
  have he : PointBox.calc p5_250.t = p5_250 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_251_contains : p5_251.Contains (quadraturePoint 5 251) := by
  have ht : p5_251.t.Contains (quadraturePoint 5 251) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨251,by decide⟩).scale 1 12) = p5_251.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨251,by decide⟩
  have he : PointBox.calc p5_251.t = p5_251 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_252_contains : p5_252.Contains (quadraturePoint 5 252) := by
  have ht : p5_252.t.Contains (quadraturePoint 5 252) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨252,by decide⟩).scale 1 12) = p5_252.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨252,by decide⟩
  have he : PointBox.calc p5_252.t = p5_252 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_253_contains : p5_253.Contains (quadraturePoint 5 253) := by
  have ht : p5_253.t.Contains (quadraturePoint 5 253) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨253,by decide⟩).scale 1 12) = p5_253.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨253,by decide⟩
  have he : PointBox.calc p5_253.t = p5_253 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_254_contains : p5_254.Contains (quadraturePoint 5 254) := by
  have ht : p5_254.t.Contains (quadraturePoint 5 254) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨254,by decide⟩).scale 1 12) = p5_254.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨254,by decide⟩
  have he : PointBox.calc p5_254.t = p5_254 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_255_contains : p5_255.Contains (quadraturePoint 5 255) := by
  have ht : p5_255.t.Contains (quadraturePoint 5 255) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨255,by decide⟩).scale 1 12) = p5_255.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨255,by decide⟩
  have he : PointBox.calc p5_255.t = p5_255 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_15_contains_g_oai (k : Fin 16) : (row5_15 k).Contains (quadraturePoint 5 (240+k.val)) := by
  fin_cases k
  · exact p5_240_contains
  · exact p5_241_contains
  · exact p5_242_contains
  · exact p5_243_contains
  · exact p5_244_contains
  · exact p5_245_contains
  · exact p5_246_contains
  · exact p5_247_contains
  · exact p5_248_contains
  · exact p5_249_contains
  · exact p5_250_contains
  · exact p5_251_contains
  · exact p5_252_contains
  · exact p5_253_contains
  · exact p5_254_contains
  · exact p5_255_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_15_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_15_contains_g_oai
