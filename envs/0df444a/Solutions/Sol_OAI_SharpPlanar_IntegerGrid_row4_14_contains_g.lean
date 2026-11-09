-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row4_14_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:30.038759+00:00
-- url     : https://prove2.me/submissions/7adf6b2a-2cd0-4ab1-ba32-e3961344ae9a

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

lemma p4_224_contains : p4_224.Contains (quadraturePoint 4 224) := by
  have ht : p4_224.t.Contains (quadraturePoint 4 224) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p4_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨224,by decide⟩
  have he : PointBox.calc p4_224.t = p4_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_225_contains : p4_225.Contains (quadraturePoint 4 225) := by
  have ht : p4_225.t.Contains (quadraturePoint 4 225) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p4_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨225,by decide⟩
  have he : PointBox.calc p4_225.t = p4_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_226_contains : p4_226.Contains (quadraturePoint 4 226) := by
  have ht : p4_226.t.Contains (quadraturePoint 4 226) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p4_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨226,by decide⟩
  have he : PointBox.calc p4_226.t = p4_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_227_contains : p4_227.Contains (quadraturePoint 4 227) := by
  have ht : p4_227.t.Contains (quadraturePoint 4 227) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p4_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨227,by decide⟩
  have he : PointBox.calc p4_227.t = p4_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_228_contains : p4_228.Contains (quadraturePoint 4 228) := by
  have ht : p4_228.t.Contains (quadraturePoint 4 228) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p4_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨228,by decide⟩
  have he : PointBox.calc p4_228.t = p4_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_229_contains : p4_229.Contains (quadraturePoint 4 229) := by
  have ht : p4_229.t.Contains (quadraturePoint 4 229) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p4_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨229,by decide⟩
  have he : PointBox.calc p4_229.t = p4_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_230_contains : p4_230.Contains (quadraturePoint 4 230) := by
  have ht : p4_230.t.Contains (quadraturePoint 4 230) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p4_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨230,by decide⟩
  have he : PointBox.calc p4_230.t = p4_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_231_contains : p4_231.Contains (quadraturePoint 4 231) := by
  have ht : p4_231.t.Contains (quadraturePoint 4 231) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p4_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨231,by decide⟩
  have he : PointBox.calc p4_231.t = p4_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_232_contains : p4_232.Contains (quadraturePoint 4 232) := by
  have ht : p4_232.t.Contains (quadraturePoint 4 232) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p4_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨232,by decide⟩
  have he : PointBox.calc p4_232.t = p4_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_233_contains : p4_233.Contains (quadraturePoint 4 233) := by
  have ht : p4_233.t.Contains (quadraturePoint 4 233) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p4_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨233,by decide⟩
  have he : PointBox.calc p4_233.t = p4_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_234_contains : p4_234.Contains (quadraturePoint 4 234) := by
  have ht : p4_234.t.Contains (quadraturePoint 4 234) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p4_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨234,by decide⟩
  have he : PointBox.calc p4_234.t = p4_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_235_contains : p4_235.Contains (quadraturePoint 4 235) := by
  have ht : p4_235.t.Contains (quadraturePoint 4 235) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p4_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨235,by decide⟩
  have he : PointBox.calc p4_235.t = p4_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_236_contains : p4_236.Contains (quadraturePoint 4 236) := by
  have ht : p4_236.t.Contains (quadraturePoint 4 236) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p4_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨236,by decide⟩
  have he : PointBox.calc p4_236.t = p4_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_237_contains : p4_237.Contains (quadraturePoint 4 237) := by
  have ht : p4_237.t.Contains (quadraturePoint 4 237) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p4_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨237,by decide⟩
  have he : PointBox.calc p4_237.t = p4_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_238_contains : p4_238.Contains (quadraturePoint 4 238) := by
  have ht : p4_238.t.Contains (quadraturePoint 4 238) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p4_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨238,by decide⟩
  have he : PointBox.calc p4_238.t = p4_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_239_contains : p4_239.Contains (quadraturePoint 4 239) := by
  have ht : p4_239.t.Contains (quadraturePoint 4 239) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p4_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨239,by decide⟩
  have he : PointBox.calc p4_239.t = p4_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row4_14_contains_g_oai (k : Fin 16) : (row4_14 k).Contains (quadraturePoint 4 (224+k.val)) := by
  fin_cases k
  · exact p4_224_contains
  · exact p4_225_contains
  · exact p4_226_contains
  · exact p4_227_contains
  · exact p4_228_contains
  · exact p4_229_contains
  · exact p4_230_contains
  · exact p4_231_contains
  · exact p4_232_contains
  · exact p4_233_contains
  · exact p4_234_contains
  · exact p4_235_contains
  · exact p4_236_contains
  · exact p4_237_contains
  · exact p4_238_contains
  · exact p4_239_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row4_14_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row4_14_contains_g_oai
