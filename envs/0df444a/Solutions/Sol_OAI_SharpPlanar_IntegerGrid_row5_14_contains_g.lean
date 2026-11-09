-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_14_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:12.023424+00:00
-- url     : https://prove2.me/submissions/4d8f75dd-4b04-4302-a380-48422c5777fa

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

lemma p5_224_contains : p5_224.Contains (quadraturePoint 5 224) := by
  have ht : p5_224.t.Contains (quadraturePoint 5 224) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p5_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨224,by decide⟩
  have he : PointBox.calc p5_224.t = p5_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_225_contains : p5_225.Contains (quadraturePoint 5 225) := by
  have ht : p5_225.t.Contains (quadraturePoint 5 225) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p5_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨225,by decide⟩
  have he : PointBox.calc p5_225.t = p5_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_226_contains : p5_226.Contains (quadraturePoint 5 226) := by
  have ht : p5_226.t.Contains (quadraturePoint 5 226) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p5_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨226,by decide⟩
  have he : PointBox.calc p5_226.t = p5_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_227_contains : p5_227.Contains (quadraturePoint 5 227) := by
  have ht : p5_227.t.Contains (quadraturePoint 5 227) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p5_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨227,by decide⟩
  have he : PointBox.calc p5_227.t = p5_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_228_contains : p5_228.Contains (quadraturePoint 5 228) := by
  have ht : p5_228.t.Contains (quadraturePoint 5 228) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p5_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨228,by decide⟩
  have he : PointBox.calc p5_228.t = p5_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_229_contains : p5_229.Contains (quadraturePoint 5 229) := by
  have ht : p5_229.t.Contains (quadraturePoint 5 229) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p5_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨229,by decide⟩
  have he : PointBox.calc p5_229.t = p5_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_230_contains : p5_230.Contains (quadraturePoint 5 230) := by
  have ht : p5_230.t.Contains (quadraturePoint 5 230) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p5_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨230,by decide⟩
  have he : PointBox.calc p5_230.t = p5_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_231_contains : p5_231.Contains (quadraturePoint 5 231) := by
  have ht : p5_231.t.Contains (quadraturePoint 5 231) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p5_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨231,by decide⟩
  have he : PointBox.calc p5_231.t = p5_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_232_contains : p5_232.Contains (quadraturePoint 5 232) := by
  have ht : p5_232.t.Contains (quadraturePoint 5 232) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p5_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨232,by decide⟩
  have he : PointBox.calc p5_232.t = p5_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_233_contains : p5_233.Contains (quadraturePoint 5 233) := by
  have ht : p5_233.t.Contains (quadraturePoint 5 233) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p5_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨233,by decide⟩
  have he : PointBox.calc p5_233.t = p5_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_234_contains : p5_234.Contains (quadraturePoint 5 234) := by
  have ht : p5_234.t.Contains (quadraturePoint 5 234) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p5_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨234,by decide⟩
  have he : PointBox.calc p5_234.t = p5_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_235_contains : p5_235.Contains (quadraturePoint 5 235) := by
  have ht : p5_235.t.Contains (quadraturePoint 5 235) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p5_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨235,by decide⟩
  have he : PointBox.calc p5_235.t = p5_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_236_contains : p5_236.Contains (quadraturePoint 5 236) := by
  have ht : p5_236.t.Contains (quadraturePoint 5 236) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p5_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨236,by decide⟩
  have he : PointBox.calc p5_236.t = p5_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_237_contains : p5_237.Contains (quadraturePoint 5 237) := by
  have ht : p5_237.t.Contains (quadraturePoint 5 237) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p5_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨237,by decide⟩
  have he : PointBox.calc p5_237.t = p5_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_238_contains : p5_238.Contains (quadraturePoint 5 238) := by
  have ht : p5_238.t.Contains (quadraturePoint 5 238) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p5_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨238,by decide⟩
  have he : PointBox.calc p5_238.t = p5_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_239_contains : p5_239.Contains (quadraturePoint 5 239) := by
  have ht : p5_239.t.Contains (quadraturePoint 5 239) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p5_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨239,by decide⟩
  have he : PointBox.calc p5_239.t = p5_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_14_contains_g_oai (k : Fin 16) : (row5_14 k).Contains (quadraturePoint 5 (224+k.val)) := by
  fin_cases k
  · exact p5_224_contains
  · exact p5_225_contains
  · exact p5_226_contains
  · exact p5_227_contains
  · exact p5_228_contains
  · exact p5_229_contains
  · exact p5_230_contains
  · exact p5_231_contains
  · exact p5_232_contains
  · exact p5_233_contains
  · exact p5_234_contains
  · exact p5_235_contains
  · exact p5_236_contains
  · exact p5_237_contains
  · exact p5_238_contains
  · exact p5_239_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_14_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_14_contains_g_oai
