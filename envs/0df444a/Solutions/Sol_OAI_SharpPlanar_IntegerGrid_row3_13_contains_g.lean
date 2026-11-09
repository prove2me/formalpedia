-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row3_13_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:45.403578+00:00
-- url     : https://prove2.me/submissions/6aa331b1-e01f-4df7-a850-949a591c98a3

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

lemma p3_208_contains : p3_208.Contains (quadraturePoint 3 208) := by
  have ht : p3_208.t.Contains (quadraturePoint 3 208) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨208,by decide⟩).scale 1 12) = p3_208.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨208,by decide⟩
  have he : PointBox.calc p3_208.t = p3_208 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_209_contains : p3_209.Contains (quadraturePoint 3 209) := by
  have ht : p3_209.t.Contains (quadraturePoint 3 209) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨209,by decide⟩).scale 1 12) = p3_209.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨209,by decide⟩
  have he : PointBox.calc p3_209.t = p3_209 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_210_contains : p3_210.Contains (quadraturePoint 3 210) := by
  have ht : p3_210.t.Contains (quadraturePoint 3 210) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨210,by decide⟩).scale 1 12) = p3_210.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨210,by decide⟩
  have he : PointBox.calc p3_210.t = p3_210 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_211_contains : p3_211.Contains (quadraturePoint 3 211) := by
  have ht : p3_211.t.Contains (quadraturePoint 3 211) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨211,by decide⟩).scale 1 12) = p3_211.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨211,by decide⟩
  have he : PointBox.calc p3_211.t = p3_211 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_212_contains : p3_212.Contains (quadraturePoint 3 212) := by
  have ht : p3_212.t.Contains (quadraturePoint 3 212) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨212,by decide⟩).scale 1 12) = p3_212.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨212,by decide⟩
  have he : PointBox.calc p3_212.t = p3_212 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_213_contains : p3_213.Contains (quadraturePoint 3 213) := by
  have ht : p3_213.t.Contains (quadraturePoint 3 213) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨213,by decide⟩).scale 1 12) = p3_213.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨213,by decide⟩
  have he : PointBox.calc p3_213.t = p3_213 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_214_contains : p3_214.Contains (quadraturePoint 3 214) := by
  have ht : p3_214.t.Contains (quadraturePoint 3 214) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨214,by decide⟩).scale 1 12) = p3_214.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨214,by decide⟩
  have he : PointBox.calc p3_214.t = p3_214 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_215_contains : p3_215.Contains (quadraturePoint 3 215) := by
  have ht : p3_215.t.Contains (quadraturePoint 3 215) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨215,by decide⟩).scale 1 12) = p3_215.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨215,by decide⟩
  have he : PointBox.calc p3_215.t = p3_215 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_216_contains : p3_216.Contains (quadraturePoint 3 216) := by
  have ht : p3_216.t.Contains (quadraturePoint 3 216) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨216,by decide⟩).scale 1 12) = p3_216.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨216,by decide⟩
  have he : PointBox.calc p3_216.t = p3_216 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_217_contains : p3_217.Contains (quadraturePoint 3 217) := by
  have ht : p3_217.t.Contains (quadraturePoint 3 217) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨217,by decide⟩).scale 1 12) = p3_217.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨217,by decide⟩
  have he : PointBox.calc p3_217.t = p3_217 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_218_contains : p3_218.Contains (quadraturePoint 3 218) := by
  have ht : p3_218.t.Contains (quadraturePoint 3 218) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨218,by decide⟩).scale 1 12) = p3_218.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨218,by decide⟩
  have he : PointBox.calc p3_218.t = p3_218 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_219_contains : p3_219.Contains (quadraturePoint 3 219) := by
  have ht : p3_219.t.Contains (quadraturePoint 3 219) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨219,by decide⟩).scale 1 12) = p3_219.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨219,by decide⟩
  have he : PointBox.calc p3_219.t = p3_219 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_220_contains : p3_220.Contains (quadraturePoint 3 220) := by
  have ht : p3_220.t.Contains (quadraturePoint 3 220) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨220,by decide⟩).scale 1 12) = p3_220.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨220,by decide⟩
  have he : PointBox.calc p3_220.t = p3_220 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_221_contains : p3_221.Contains (quadraturePoint 3 221) := by
  have ht : p3_221.t.Contains (quadraturePoint 3 221) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨221,by decide⟩).scale 1 12) = p3_221.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨221,by decide⟩
  have he : PointBox.calc p3_221.t = p3_221 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_222_contains : p3_222.Contains (quadraturePoint 3 222) := by
  have ht : p3_222.t.Contains (quadraturePoint 3 222) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨222,by decide⟩).scale 1 12) = p3_222.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨222,by decide⟩
  have he : PointBox.calc p3_222.t = p3_222 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_223_contains : p3_223.Contains (quadraturePoint 3 223) := by
  have ht : p3_223.t.Contains (quadraturePoint 3 223) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨223,by decide⟩).scale 1 12) = p3_223.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨223,by decide⟩
  have he : PointBox.calc p3_223.t = p3_223 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row3_13_contains_g_oai (k : Fin 16) : (row3_13 k).Contains (quadraturePoint 3 (208+k.val)) := by
  fin_cases k
  · exact p3_208_contains
  · exact p3_209_contains
  · exact p3_210_contains
  · exact p3_211_contains
  · exact p3_212_contains
  · exact p3_213_contains
  · exact p3_214_contains
  · exact p3_215_contains
  · exact p3_216_contains
  · exact p3_217_contains
  · exact p3_218_contains
  · exact p3_219_contains
  · exact p3_220_contains
  · exact p3_221_contains
  · exact p3_222_contains
  · exact p3_223_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row3_13_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row3_13_contains_g_oai
