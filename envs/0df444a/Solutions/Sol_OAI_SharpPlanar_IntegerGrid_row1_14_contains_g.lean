-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_14_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:13.206194+00:00
-- url     : https://prove2.me/submissions/8f4d8876-f816-4ac4-b533-9cd8d00bad95

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

lemma p1_224_contains : p1_224.Contains (quadraturePoint 1 224) := by
  have ht : p1_224.t.Contains (quadraturePoint 1 224) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p1_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨224,by decide⟩
  have he : PointBox.calc p1_224.t = p1_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_225_contains : p1_225.Contains (quadraturePoint 1 225) := by
  have ht : p1_225.t.Contains (quadraturePoint 1 225) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p1_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨225,by decide⟩
  have he : PointBox.calc p1_225.t = p1_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_226_contains : p1_226.Contains (quadraturePoint 1 226) := by
  have ht : p1_226.t.Contains (quadraturePoint 1 226) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p1_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨226,by decide⟩
  have he : PointBox.calc p1_226.t = p1_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_227_contains : p1_227.Contains (quadraturePoint 1 227) := by
  have ht : p1_227.t.Contains (quadraturePoint 1 227) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p1_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨227,by decide⟩
  have he : PointBox.calc p1_227.t = p1_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_228_contains : p1_228.Contains (quadraturePoint 1 228) := by
  have ht : p1_228.t.Contains (quadraturePoint 1 228) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p1_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨228,by decide⟩
  have he : PointBox.calc p1_228.t = p1_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_229_contains : p1_229.Contains (quadraturePoint 1 229) := by
  have ht : p1_229.t.Contains (quadraturePoint 1 229) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p1_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨229,by decide⟩
  have he : PointBox.calc p1_229.t = p1_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_230_contains : p1_230.Contains (quadraturePoint 1 230) := by
  have ht : p1_230.t.Contains (quadraturePoint 1 230) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p1_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨230,by decide⟩
  have he : PointBox.calc p1_230.t = p1_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_231_contains : p1_231.Contains (quadraturePoint 1 231) := by
  have ht : p1_231.t.Contains (quadraturePoint 1 231) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p1_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨231,by decide⟩
  have he : PointBox.calc p1_231.t = p1_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_232_contains : p1_232.Contains (quadraturePoint 1 232) := by
  have ht : p1_232.t.Contains (quadraturePoint 1 232) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p1_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨232,by decide⟩
  have he : PointBox.calc p1_232.t = p1_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_233_contains : p1_233.Contains (quadraturePoint 1 233) := by
  have ht : p1_233.t.Contains (quadraturePoint 1 233) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p1_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨233,by decide⟩
  have he : PointBox.calc p1_233.t = p1_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_234_contains : p1_234.Contains (quadraturePoint 1 234) := by
  have ht : p1_234.t.Contains (quadraturePoint 1 234) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p1_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨234,by decide⟩
  have he : PointBox.calc p1_234.t = p1_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_235_contains : p1_235.Contains (quadraturePoint 1 235) := by
  have ht : p1_235.t.Contains (quadraturePoint 1 235) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p1_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨235,by decide⟩
  have he : PointBox.calc p1_235.t = p1_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_236_contains : p1_236.Contains (quadraturePoint 1 236) := by
  have ht : p1_236.t.Contains (quadraturePoint 1 236) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p1_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨236,by decide⟩
  have he : PointBox.calc p1_236.t = p1_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_237_contains : p1_237.Contains (quadraturePoint 1 237) := by
  have ht : p1_237.t.Contains (quadraturePoint 1 237) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p1_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨237,by decide⟩
  have he : PointBox.calc p1_237.t = p1_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_238_contains : p1_238.Contains (quadraturePoint 1 238) := by
  have ht : p1_238.t.Contains (quadraturePoint 1 238) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p1_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨238,by decide⟩
  have he : PointBox.calc p1_238.t = p1_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_239_contains : p1_239.Contains (quadraturePoint 1 239) := by
  have ht : p1_239.t.Contains (quadraturePoint 1 239) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p1_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨239,by decide⟩
  have he : PointBox.calc p1_239.t = p1_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_14_contains_g_oai (k : Fin 16) : (row1_14 k).Contains (quadraturePoint 1 (224+k.val)) := by
  fin_cases k
  · exact p1_224_contains
  · exact p1_225_contains
  · exact p1_226_contains
  · exact p1_227_contains
  · exact p1_228_contains
  · exact p1_229_contains
  · exact p1_230_contains
  · exact p1_231_contains
  · exact p1_232_contains
  · exact p1_233_contains
  · exact p1_234_contains
  · exact p1_235_contains
  · exact p1_236_contains
  · exact p1_237_contains
  · exact p1_238_contains
  · exact p1_239_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_14_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_14_contains_g_oai
