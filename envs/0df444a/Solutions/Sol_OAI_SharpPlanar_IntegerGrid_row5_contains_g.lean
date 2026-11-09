-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:12.783045+00:00
-- url     : https://prove2.me/submissions/55f77d9a-8a97-4624-86f8-a82635810666

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_14_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_7_contains_g
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

lemma p5_0_contains : p5_0.Contains (quadraturePoint 5 0) := by
  have ht : p5_0.t.Contains (quadraturePoint 5 0) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p5_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨0,by decide⟩
  have he : PointBox.calc p5_0.t = p5_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_1_contains : p5_1.Contains (quadraturePoint 5 1) := by
  have ht : p5_1.t.Contains (quadraturePoint 5 1) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p5_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨1,by decide⟩
  have he : PointBox.calc p5_1.t = p5_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_2_contains : p5_2.Contains (quadraturePoint 5 2) := by
  have ht : p5_2.t.Contains (quadraturePoint 5 2) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p5_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨2,by decide⟩
  have he : PointBox.calc p5_2.t = p5_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_3_contains : p5_3.Contains (quadraturePoint 5 3) := by
  have ht : p5_3.t.Contains (quadraturePoint 5 3) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p5_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨3,by decide⟩
  have he : PointBox.calc p5_3.t = p5_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_4_contains : p5_4.Contains (quadraturePoint 5 4) := by
  have ht : p5_4.t.Contains (quadraturePoint 5 4) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p5_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨4,by decide⟩
  have he : PointBox.calc p5_4.t = p5_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_5_contains : p5_5.Contains (quadraturePoint 5 5) := by
  have ht : p5_5.t.Contains (quadraturePoint 5 5) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p5_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨5,by decide⟩
  have he : PointBox.calc p5_5.t = p5_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_6_contains : p5_6.Contains (quadraturePoint 5 6) := by
  have ht : p5_6.t.Contains (quadraturePoint 5 6) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p5_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨6,by decide⟩
  have he : PointBox.calc p5_6.t = p5_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_7_contains : p5_7.Contains (quadraturePoint 5 7) := by
  have ht : p5_7.t.Contains (quadraturePoint 5 7) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p5_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨7,by decide⟩
  have he : PointBox.calc p5_7.t = p5_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_8_contains : p5_8.Contains (quadraturePoint 5 8) := by
  have ht : p5_8.t.Contains (quadraturePoint 5 8) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p5_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨8,by decide⟩
  have he : PointBox.calc p5_8.t = p5_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_9_contains : p5_9.Contains (quadraturePoint 5 9) := by
  have ht : p5_9.t.Contains (quadraturePoint 5 9) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p5_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨9,by decide⟩
  have he : PointBox.calc p5_9.t = p5_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_10_contains : p5_10.Contains (quadraturePoint 5 10) := by
  have ht : p5_10.t.Contains (quadraturePoint 5 10) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p5_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨10,by decide⟩
  have he : PointBox.calc p5_10.t = p5_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_11_contains : p5_11.Contains (quadraturePoint 5 11) := by
  have ht : p5_11.t.Contains (quadraturePoint 5 11) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p5_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨11,by decide⟩
  have he : PointBox.calc p5_11.t = p5_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_12_contains : p5_12.Contains (quadraturePoint 5 12) := by
  have ht : p5_12.t.Contains (quadraturePoint 5 12) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p5_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨12,by decide⟩
  have he : PointBox.calc p5_12.t = p5_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_13_contains : p5_13.Contains (quadraturePoint 5 13) := by
  have ht : p5_13.t.Contains (quadraturePoint 5 13) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p5_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨13,by decide⟩
  have he : PointBox.calc p5_13.t = p5_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_14_contains : p5_14.Contains (quadraturePoint 5 14) := by
  have ht : p5_14.t.Contains (quadraturePoint 5 14) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p5_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨14,by decide⟩
  have he : PointBox.calc p5_14.t = p5_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_15_contains : p5_15.Contains (quadraturePoint 5 15) := by
  have ht : p5_15.t.Contains (quadraturePoint 5 15) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p5_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨15,by decide⟩
  have he : PointBox.calc p5_15.t = p5_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_16_contains : p5_16.Contains (quadraturePoint 5 16) := by
  have ht : p5_16.t.Contains (quadraturePoint 5 16) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p5_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨16,by decide⟩
  have he : PointBox.calc p5_16.t = p5_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_17_contains : p5_17.Contains (quadraturePoint 5 17) := by
  have ht : p5_17.t.Contains (quadraturePoint 5 17) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p5_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨17,by decide⟩
  have he : PointBox.calc p5_17.t = p5_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_18_contains : p5_18.Contains (quadraturePoint 5 18) := by
  have ht : p5_18.t.Contains (quadraturePoint 5 18) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p5_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨18,by decide⟩
  have he : PointBox.calc p5_18.t = p5_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_19_contains : p5_19.Contains (quadraturePoint 5 19) := by
  have ht : p5_19.t.Contains (quadraturePoint 5 19) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p5_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨19,by decide⟩
  have he : PointBox.calc p5_19.t = p5_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_20_contains : p5_20.Contains (quadraturePoint 5 20) := by
  have ht : p5_20.t.Contains (quadraturePoint 5 20) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p5_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨20,by decide⟩
  have he : PointBox.calc p5_20.t = p5_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_21_contains : p5_21.Contains (quadraturePoint 5 21) := by
  have ht : p5_21.t.Contains (quadraturePoint 5 21) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p5_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨21,by decide⟩
  have he : PointBox.calc p5_21.t = p5_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_22_contains : p5_22.Contains (quadraturePoint 5 22) := by
  have ht : p5_22.t.Contains (quadraturePoint 5 22) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p5_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨22,by decide⟩
  have he : PointBox.calc p5_22.t = p5_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_23_contains : p5_23.Contains (quadraturePoint 5 23) := by
  have ht : p5_23.t.Contains (quadraturePoint 5 23) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p5_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨23,by decide⟩
  have he : PointBox.calc p5_23.t = p5_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_24_contains : p5_24.Contains (quadraturePoint 5 24) := by
  have ht : p5_24.t.Contains (quadraturePoint 5 24) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p5_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨24,by decide⟩
  have he : PointBox.calc p5_24.t = p5_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_25_contains : p5_25.Contains (quadraturePoint 5 25) := by
  have ht : p5_25.t.Contains (quadraturePoint 5 25) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p5_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨25,by decide⟩
  have he : PointBox.calc p5_25.t = p5_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_26_contains : p5_26.Contains (quadraturePoint 5 26) := by
  have ht : p5_26.t.Contains (quadraturePoint 5 26) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p5_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨26,by decide⟩
  have he : PointBox.calc p5_26.t = p5_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_27_contains : p5_27.Contains (quadraturePoint 5 27) := by
  have ht : p5_27.t.Contains (quadraturePoint 5 27) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p5_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨27,by decide⟩
  have he : PointBox.calc p5_27.t = p5_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_28_contains : p5_28.Contains (quadraturePoint 5 28) := by
  have ht : p5_28.t.Contains (quadraturePoint 5 28) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p5_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨28,by decide⟩
  have he : PointBox.calc p5_28.t = p5_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_29_contains : p5_29.Contains (quadraturePoint 5 29) := by
  have ht : p5_29.t.Contains (quadraturePoint 5 29) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p5_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨29,by decide⟩
  have he : PointBox.calc p5_29.t = p5_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_30_contains : p5_30.Contains (quadraturePoint 5 30) := by
  have ht : p5_30.t.Contains (quadraturePoint 5 30) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p5_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨30,by decide⟩
  have he : PointBox.calc p5_30.t = p5_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_31_contains : p5_31.Contains (quadraturePoint 5 31) := by
  have ht : p5_31.t.Contains (quadraturePoint 5 31) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p5_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨31,by decide⟩
  have he : PointBox.calc p5_31.t = p5_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_32_contains : p5_32.Contains (quadraturePoint 5 32) := by
  have ht : p5_32.t.Contains (quadraturePoint 5 32) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨32,by decide⟩).scale 1 12) = p5_32.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨32,by decide⟩
  have he : PointBox.calc p5_32.t = p5_32 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_33_contains : p5_33.Contains (quadraturePoint 5 33) := by
  have ht : p5_33.t.Contains (quadraturePoint 5 33) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨33,by decide⟩).scale 1 12) = p5_33.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨33,by decide⟩
  have he : PointBox.calc p5_33.t = p5_33 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_34_contains : p5_34.Contains (quadraturePoint 5 34) := by
  have ht : p5_34.t.Contains (quadraturePoint 5 34) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨34,by decide⟩).scale 1 12) = p5_34.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨34,by decide⟩
  have he : PointBox.calc p5_34.t = p5_34 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_35_contains : p5_35.Contains (quadraturePoint 5 35) := by
  have ht : p5_35.t.Contains (quadraturePoint 5 35) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨35,by decide⟩).scale 1 12) = p5_35.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨35,by decide⟩
  have he : PointBox.calc p5_35.t = p5_35 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_36_contains : p5_36.Contains (quadraturePoint 5 36) := by
  have ht : p5_36.t.Contains (quadraturePoint 5 36) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨36,by decide⟩).scale 1 12) = p5_36.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨36,by decide⟩
  have he : PointBox.calc p5_36.t = p5_36 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_37_contains : p5_37.Contains (quadraturePoint 5 37) := by
  have ht : p5_37.t.Contains (quadraturePoint 5 37) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨37,by decide⟩).scale 1 12) = p5_37.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨37,by decide⟩
  have he : PointBox.calc p5_37.t = p5_37 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_38_contains : p5_38.Contains (quadraturePoint 5 38) := by
  have ht : p5_38.t.Contains (quadraturePoint 5 38) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨38,by decide⟩).scale 1 12) = p5_38.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨38,by decide⟩
  have he : PointBox.calc p5_38.t = p5_38 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_39_contains : p5_39.Contains (quadraturePoint 5 39) := by
  have ht : p5_39.t.Contains (quadraturePoint 5 39) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨39,by decide⟩).scale 1 12) = p5_39.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨39,by decide⟩
  have he : PointBox.calc p5_39.t = p5_39 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_40_contains : p5_40.Contains (quadraturePoint 5 40) := by
  have ht : p5_40.t.Contains (quadraturePoint 5 40) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨40,by decide⟩).scale 1 12) = p5_40.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨40,by decide⟩
  have he : PointBox.calc p5_40.t = p5_40 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_41_contains : p5_41.Contains (quadraturePoint 5 41) := by
  have ht : p5_41.t.Contains (quadraturePoint 5 41) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨41,by decide⟩).scale 1 12) = p5_41.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨41,by decide⟩
  have he : PointBox.calc p5_41.t = p5_41 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_42_contains : p5_42.Contains (quadraturePoint 5 42) := by
  have ht : p5_42.t.Contains (quadraturePoint 5 42) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨42,by decide⟩).scale 1 12) = p5_42.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨42,by decide⟩
  have he : PointBox.calc p5_42.t = p5_42 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_43_contains : p5_43.Contains (quadraturePoint 5 43) := by
  have ht : p5_43.t.Contains (quadraturePoint 5 43) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨43,by decide⟩).scale 1 12) = p5_43.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨43,by decide⟩
  have he : PointBox.calc p5_43.t = p5_43 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_44_contains : p5_44.Contains (quadraturePoint 5 44) := by
  have ht : p5_44.t.Contains (quadraturePoint 5 44) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨44,by decide⟩).scale 1 12) = p5_44.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨44,by decide⟩
  have he : PointBox.calc p5_44.t = p5_44 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_45_contains : p5_45.Contains (quadraturePoint 5 45) := by
  have ht : p5_45.t.Contains (quadraturePoint 5 45) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨45,by decide⟩).scale 1 12) = p5_45.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨45,by decide⟩
  have he : PointBox.calc p5_45.t = p5_45 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_46_contains : p5_46.Contains (quadraturePoint 5 46) := by
  have ht : p5_46.t.Contains (quadraturePoint 5 46) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨46,by decide⟩).scale 1 12) = p5_46.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨46,by decide⟩
  have he : PointBox.calc p5_46.t = p5_46 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_47_contains : p5_47.Contains (quadraturePoint 5 47) := by
  have ht : p5_47.t.Contains (quadraturePoint 5 47) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨47,by decide⟩).scale 1 12) = p5_47.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨47,by decide⟩
  have he : PointBox.calc p5_47.t = p5_47 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_48_contains : p5_48.Contains (quadraturePoint 5 48) := by
  have ht : p5_48.t.Contains (quadraturePoint 5 48) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p5_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨48,by decide⟩
  have he : PointBox.calc p5_48.t = p5_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_49_contains : p5_49.Contains (quadraturePoint 5 49) := by
  have ht : p5_49.t.Contains (quadraturePoint 5 49) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p5_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨49,by decide⟩
  have he : PointBox.calc p5_49.t = p5_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_50_contains : p5_50.Contains (quadraturePoint 5 50) := by
  have ht : p5_50.t.Contains (quadraturePoint 5 50) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p5_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨50,by decide⟩
  have he : PointBox.calc p5_50.t = p5_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_51_contains : p5_51.Contains (quadraturePoint 5 51) := by
  have ht : p5_51.t.Contains (quadraturePoint 5 51) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p5_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨51,by decide⟩
  have he : PointBox.calc p5_51.t = p5_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_52_contains : p5_52.Contains (quadraturePoint 5 52) := by
  have ht : p5_52.t.Contains (quadraturePoint 5 52) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p5_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨52,by decide⟩
  have he : PointBox.calc p5_52.t = p5_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_53_contains : p5_53.Contains (quadraturePoint 5 53) := by
  have ht : p5_53.t.Contains (quadraturePoint 5 53) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p5_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨53,by decide⟩
  have he : PointBox.calc p5_53.t = p5_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_54_contains : p5_54.Contains (quadraturePoint 5 54) := by
  have ht : p5_54.t.Contains (quadraturePoint 5 54) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p5_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨54,by decide⟩
  have he : PointBox.calc p5_54.t = p5_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_55_contains : p5_55.Contains (quadraturePoint 5 55) := by
  have ht : p5_55.t.Contains (quadraturePoint 5 55) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p5_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨55,by decide⟩
  have he : PointBox.calc p5_55.t = p5_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_56_contains : p5_56.Contains (quadraturePoint 5 56) := by
  have ht : p5_56.t.Contains (quadraturePoint 5 56) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p5_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨56,by decide⟩
  have he : PointBox.calc p5_56.t = p5_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_57_contains : p5_57.Contains (quadraturePoint 5 57) := by
  have ht : p5_57.t.Contains (quadraturePoint 5 57) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p5_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨57,by decide⟩
  have he : PointBox.calc p5_57.t = p5_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_58_contains : p5_58.Contains (quadraturePoint 5 58) := by
  have ht : p5_58.t.Contains (quadraturePoint 5 58) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p5_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨58,by decide⟩
  have he : PointBox.calc p5_58.t = p5_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_59_contains : p5_59.Contains (quadraturePoint 5 59) := by
  have ht : p5_59.t.Contains (quadraturePoint 5 59) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p5_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨59,by decide⟩
  have he : PointBox.calc p5_59.t = p5_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_60_contains : p5_60.Contains (quadraturePoint 5 60) := by
  have ht : p5_60.t.Contains (quadraturePoint 5 60) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p5_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨60,by decide⟩
  have he : PointBox.calc p5_60.t = p5_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_61_contains : p5_61.Contains (quadraturePoint 5 61) := by
  have ht : p5_61.t.Contains (quadraturePoint 5 61) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p5_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨61,by decide⟩
  have he : PointBox.calc p5_61.t = p5_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_62_contains : p5_62.Contains (quadraturePoint 5 62) := by
  have ht : p5_62.t.Contains (quadraturePoint 5 62) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p5_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨62,by decide⟩
  have he : PointBox.calc p5_62.t = p5_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_63_contains : p5_63.Contains (quadraturePoint 5 63) := by
  have ht : p5_63.t.Contains (quadraturePoint 5 63) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p5_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨63,by decide⟩
  have he : PointBox.calc p5_63.t = p5_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_64_contains : p5_64.Contains (quadraturePoint 5 64) := by
  have ht : p5_64.t.Contains (quadraturePoint 5 64) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p5_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨64,by decide⟩
  have he : PointBox.calc p5_64.t = p5_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_65_contains : p5_65.Contains (quadraturePoint 5 65) := by
  have ht : p5_65.t.Contains (quadraturePoint 5 65) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p5_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨65,by decide⟩
  have he : PointBox.calc p5_65.t = p5_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_66_contains : p5_66.Contains (quadraturePoint 5 66) := by
  have ht : p5_66.t.Contains (quadraturePoint 5 66) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p5_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨66,by decide⟩
  have he : PointBox.calc p5_66.t = p5_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_67_contains : p5_67.Contains (quadraturePoint 5 67) := by
  have ht : p5_67.t.Contains (quadraturePoint 5 67) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p5_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨67,by decide⟩
  have he : PointBox.calc p5_67.t = p5_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_68_contains : p5_68.Contains (quadraturePoint 5 68) := by
  have ht : p5_68.t.Contains (quadraturePoint 5 68) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p5_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨68,by decide⟩
  have he : PointBox.calc p5_68.t = p5_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_69_contains : p5_69.Contains (quadraturePoint 5 69) := by
  have ht : p5_69.t.Contains (quadraturePoint 5 69) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p5_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨69,by decide⟩
  have he : PointBox.calc p5_69.t = p5_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_70_contains : p5_70.Contains (quadraturePoint 5 70) := by
  have ht : p5_70.t.Contains (quadraturePoint 5 70) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p5_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨70,by decide⟩
  have he : PointBox.calc p5_70.t = p5_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_71_contains : p5_71.Contains (quadraturePoint 5 71) := by
  have ht : p5_71.t.Contains (quadraturePoint 5 71) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p5_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨71,by decide⟩
  have he : PointBox.calc p5_71.t = p5_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_72_contains : p5_72.Contains (quadraturePoint 5 72) := by
  have ht : p5_72.t.Contains (quadraturePoint 5 72) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p5_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨72,by decide⟩
  have he : PointBox.calc p5_72.t = p5_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_73_contains : p5_73.Contains (quadraturePoint 5 73) := by
  have ht : p5_73.t.Contains (quadraturePoint 5 73) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p5_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨73,by decide⟩
  have he : PointBox.calc p5_73.t = p5_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_74_contains : p5_74.Contains (quadraturePoint 5 74) := by
  have ht : p5_74.t.Contains (quadraturePoint 5 74) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p5_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨74,by decide⟩
  have he : PointBox.calc p5_74.t = p5_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_75_contains : p5_75.Contains (quadraturePoint 5 75) := by
  have ht : p5_75.t.Contains (quadraturePoint 5 75) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p5_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨75,by decide⟩
  have he : PointBox.calc p5_75.t = p5_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_76_contains : p5_76.Contains (quadraturePoint 5 76) := by
  have ht : p5_76.t.Contains (quadraturePoint 5 76) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p5_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨76,by decide⟩
  have he : PointBox.calc p5_76.t = p5_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_77_contains : p5_77.Contains (quadraturePoint 5 77) := by
  have ht : p5_77.t.Contains (quadraturePoint 5 77) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p5_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨77,by decide⟩
  have he : PointBox.calc p5_77.t = p5_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_78_contains : p5_78.Contains (quadraturePoint 5 78) := by
  have ht : p5_78.t.Contains (quadraturePoint 5 78) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p5_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨78,by decide⟩
  have he : PointBox.calc p5_78.t = p5_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_79_contains : p5_79.Contains (quadraturePoint 5 79) := by
  have ht : p5_79.t.Contains (quadraturePoint 5 79) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p5_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨79,by decide⟩
  have he : PointBox.calc p5_79.t = p5_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_80_contains : p5_80.Contains (quadraturePoint 5 80) := by
  have ht : p5_80.t.Contains (quadraturePoint 5 80) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p5_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨80,by decide⟩
  have he : PointBox.calc p5_80.t = p5_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_81_contains : p5_81.Contains (quadraturePoint 5 81) := by
  have ht : p5_81.t.Contains (quadraturePoint 5 81) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p5_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨81,by decide⟩
  have he : PointBox.calc p5_81.t = p5_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_82_contains : p5_82.Contains (quadraturePoint 5 82) := by
  have ht : p5_82.t.Contains (quadraturePoint 5 82) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p5_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨82,by decide⟩
  have he : PointBox.calc p5_82.t = p5_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_83_contains : p5_83.Contains (quadraturePoint 5 83) := by
  have ht : p5_83.t.Contains (quadraturePoint 5 83) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p5_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨83,by decide⟩
  have he : PointBox.calc p5_83.t = p5_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_84_contains : p5_84.Contains (quadraturePoint 5 84) := by
  have ht : p5_84.t.Contains (quadraturePoint 5 84) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p5_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨84,by decide⟩
  have he : PointBox.calc p5_84.t = p5_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_85_contains : p5_85.Contains (quadraturePoint 5 85) := by
  have ht : p5_85.t.Contains (quadraturePoint 5 85) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p5_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨85,by decide⟩
  have he : PointBox.calc p5_85.t = p5_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_86_contains : p5_86.Contains (quadraturePoint 5 86) := by
  have ht : p5_86.t.Contains (quadraturePoint 5 86) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p5_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨86,by decide⟩
  have he : PointBox.calc p5_86.t = p5_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_87_contains : p5_87.Contains (quadraturePoint 5 87) := by
  have ht : p5_87.t.Contains (quadraturePoint 5 87) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p5_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨87,by decide⟩
  have he : PointBox.calc p5_87.t = p5_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_88_contains : p5_88.Contains (quadraturePoint 5 88) := by
  have ht : p5_88.t.Contains (quadraturePoint 5 88) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p5_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨88,by decide⟩
  have he : PointBox.calc p5_88.t = p5_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_89_contains : p5_89.Contains (quadraturePoint 5 89) := by
  have ht : p5_89.t.Contains (quadraturePoint 5 89) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p5_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨89,by decide⟩
  have he : PointBox.calc p5_89.t = p5_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_90_contains : p5_90.Contains (quadraturePoint 5 90) := by
  have ht : p5_90.t.Contains (quadraturePoint 5 90) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p5_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨90,by decide⟩
  have he : PointBox.calc p5_90.t = p5_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_91_contains : p5_91.Contains (quadraturePoint 5 91) := by
  have ht : p5_91.t.Contains (quadraturePoint 5 91) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p5_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨91,by decide⟩
  have he : PointBox.calc p5_91.t = p5_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_92_contains : p5_92.Contains (quadraturePoint 5 92) := by
  have ht : p5_92.t.Contains (quadraturePoint 5 92) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p5_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨92,by decide⟩
  have he : PointBox.calc p5_92.t = p5_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_93_contains : p5_93.Contains (quadraturePoint 5 93) := by
  have ht : p5_93.t.Contains (quadraturePoint 5 93) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p5_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨93,by decide⟩
  have he : PointBox.calc p5_93.t = p5_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_94_contains : p5_94.Contains (quadraturePoint 5 94) := by
  have ht : p5_94.t.Contains (quadraturePoint 5 94) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p5_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨94,by decide⟩
  have he : PointBox.calc p5_94.t = p5_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_95_contains : p5_95.Contains (quadraturePoint 5 95) := by
  have ht : p5_95.t.Contains (quadraturePoint 5 95) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p5_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨95,by decide⟩
  have he : PointBox.calc p5_95.t = p5_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_96_contains : p5_96.Contains (quadraturePoint 5 96) := by
  have ht : p5_96.t.Contains (quadraturePoint 5 96) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨96,by decide⟩).scale 1 12) = p5_96.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨96,by decide⟩
  have he : PointBox.calc p5_96.t = p5_96 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_97_contains : p5_97.Contains (quadraturePoint 5 97) := by
  have ht : p5_97.t.Contains (quadraturePoint 5 97) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p5_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨97,by decide⟩
  have he : PointBox.calc p5_97.t = p5_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_98_contains : p5_98.Contains (quadraturePoint 5 98) := by
  have ht : p5_98.t.Contains (quadraturePoint 5 98) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨98,by decide⟩).scale 1 12) = p5_98.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨98,by decide⟩
  have he : PointBox.calc p5_98.t = p5_98 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_99_contains : p5_99.Contains (quadraturePoint 5 99) := by
  have ht : p5_99.t.Contains (quadraturePoint 5 99) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨99,by decide⟩).scale 1 12) = p5_99.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨99,by decide⟩
  have he : PointBox.calc p5_99.t = p5_99 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_100_contains : p5_100.Contains (quadraturePoint 5 100) := by
  have ht : p5_100.t.Contains (quadraturePoint 5 100) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨100,by decide⟩).scale 1 12) = p5_100.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨100,by decide⟩
  have he : PointBox.calc p5_100.t = p5_100 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_101_contains : p5_101.Contains (quadraturePoint 5 101) := by
  have ht : p5_101.t.Contains (quadraturePoint 5 101) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨101,by decide⟩).scale 1 12) = p5_101.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨101,by decide⟩
  have he : PointBox.calc p5_101.t = p5_101 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_102_contains : p5_102.Contains (quadraturePoint 5 102) := by
  have ht : p5_102.t.Contains (quadraturePoint 5 102) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨102,by decide⟩).scale 1 12) = p5_102.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨102,by decide⟩
  have he : PointBox.calc p5_102.t = p5_102 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_103_contains : p5_103.Contains (quadraturePoint 5 103) := by
  have ht : p5_103.t.Contains (quadraturePoint 5 103) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨103,by decide⟩).scale 1 12) = p5_103.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨103,by decide⟩
  have he : PointBox.calc p5_103.t = p5_103 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_104_contains : p5_104.Contains (quadraturePoint 5 104) := by
  have ht : p5_104.t.Contains (quadraturePoint 5 104) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨104,by decide⟩).scale 1 12) = p5_104.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨104,by decide⟩
  have he : PointBox.calc p5_104.t = p5_104 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_105_contains : p5_105.Contains (quadraturePoint 5 105) := by
  have ht : p5_105.t.Contains (quadraturePoint 5 105) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨105,by decide⟩).scale 1 12) = p5_105.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨105,by decide⟩
  have he : PointBox.calc p5_105.t = p5_105 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_106_contains : p5_106.Contains (quadraturePoint 5 106) := by
  have ht : p5_106.t.Contains (quadraturePoint 5 106) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨106,by decide⟩).scale 1 12) = p5_106.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨106,by decide⟩
  have he : PointBox.calc p5_106.t = p5_106 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_107_contains : p5_107.Contains (quadraturePoint 5 107) := by
  have ht : p5_107.t.Contains (quadraturePoint 5 107) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨107,by decide⟩).scale 1 12) = p5_107.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨107,by decide⟩
  have he : PointBox.calc p5_107.t = p5_107 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_108_contains : p5_108.Contains (quadraturePoint 5 108) := by
  have ht : p5_108.t.Contains (quadraturePoint 5 108) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨108,by decide⟩).scale 1 12) = p5_108.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨108,by decide⟩
  have he : PointBox.calc p5_108.t = p5_108 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_109_contains : p5_109.Contains (quadraturePoint 5 109) := by
  have ht : p5_109.t.Contains (quadraturePoint 5 109) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨109,by decide⟩).scale 1 12) = p5_109.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨109,by decide⟩
  have he : PointBox.calc p5_109.t = p5_109 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_110_contains : p5_110.Contains (quadraturePoint 5 110) := by
  have ht : p5_110.t.Contains (quadraturePoint 5 110) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨110,by decide⟩).scale 1 12) = p5_110.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨110,by decide⟩
  have he : PointBox.calc p5_110.t = p5_110 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_111_contains : p5_111.Contains (quadraturePoint 5 111) := by
  have ht : p5_111.t.Contains (quadraturePoint 5 111) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨111,by decide⟩).scale 1 12) = p5_111.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨111,by decide⟩
  have he : PointBox.calc p5_111.t = p5_111 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_128_contains : p5_128.Contains (quadraturePoint 5 128) := by
  have ht : p5_128.t.Contains (quadraturePoint 5 128) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨128,by decide⟩).scale 1 12) = p5_128.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨128,by decide⟩
  have he : PointBox.calc p5_128.t = p5_128 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_129_contains : p5_129.Contains (quadraturePoint 5 129) := by
  have ht : p5_129.t.Contains (quadraturePoint 5 129) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨129,by decide⟩).scale 1 12) = p5_129.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨129,by decide⟩
  have he : PointBox.calc p5_129.t = p5_129 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_130_contains : p5_130.Contains (quadraturePoint 5 130) := by
  have ht : p5_130.t.Contains (quadraturePoint 5 130) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨130,by decide⟩).scale 1 12) = p5_130.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨130,by decide⟩
  have he : PointBox.calc p5_130.t = p5_130 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_131_contains : p5_131.Contains (quadraturePoint 5 131) := by
  have ht : p5_131.t.Contains (quadraturePoint 5 131) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨131,by decide⟩).scale 1 12) = p5_131.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨131,by decide⟩
  have he : PointBox.calc p5_131.t = p5_131 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_132_contains : p5_132.Contains (quadraturePoint 5 132) := by
  have ht : p5_132.t.Contains (quadraturePoint 5 132) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨132,by decide⟩).scale 1 12) = p5_132.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨132,by decide⟩
  have he : PointBox.calc p5_132.t = p5_132 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_133_contains : p5_133.Contains (quadraturePoint 5 133) := by
  have ht : p5_133.t.Contains (quadraturePoint 5 133) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨133,by decide⟩).scale 1 12) = p5_133.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨133,by decide⟩
  have he : PointBox.calc p5_133.t = p5_133 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_134_contains : p5_134.Contains (quadraturePoint 5 134) := by
  have ht : p5_134.t.Contains (quadraturePoint 5 134) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨134,by decide⟩).scale 1 12) = p5_134.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨134,by decide⟩
  have he : PointBox.calc p5_134.t = p5_134 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_135_contains : p5_135.Contains (quadraturePoint 5 135) := by
  have ht : p5_135.t.Contains (quadraturePoint 5 135) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨135,by decide⟩).scale 1 12) = p5_135.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨135,by decide⟩
  have he : PointBox.calc p5_135.t = p5_135 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_136_contains : p5_136.Contains (quadraturePoint 5 136) := by
  have ht : p5_136.t.Contains (quadraturePoint 5 136) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨136,by decide⟩).scale 1 12) = p5_136.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨136,by decide⟩
  have he : PointBox.calc p5_136.t = p5_136 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_137_contains : p5_137.Contains (quadraturePoint 5 137) := by
  have ht : p5_137.t.Contains (quadraturePoint 5 137) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨137,by decide⟩).scale 1 12) = p5_137.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨137,by decide⟩
  have he : PointBox.calc p5_137.t = p5_137 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_138_contains : p5_138.Contains (quadraturePoint 5 138) := by
  have ht : p5_138.t.Contains (quadraturePoint 5 138) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨138,by decide⟩).scale 1 12) = p5_138.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨138,by decide⟩
  have he : PointBox.calc p5_138.t = p5_138 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_139_contains : p5_139.Contains (quadraturePoint 5 139) := by
  have ht : p5_139.t.Contains (quadraturePoint 5 139) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨139,by decide⟩).scale 1 12) = p5_139.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨139,by decide⟩
  have he : PointBox.calc p5_139.t = p5_139 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_140_contains : p5_140.Contains (quadraturePoint 5 140) := by
  have ht : p5_140.t.Contains (quadraturePoint 5 140) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨140,by decide⟩).scale 1 12) = p5_140.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨140,by decide⟩
  have he : PointBox.calc p5_140.t = p5_140 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_141_contains : p5_141.Contains (quadraturePoint 5 141) := by
  have ht : p5_141.t.Contains (quadraturePoint 5 141) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨141,by decide⟩).scale 1 12) = p5_141.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨141,by decide⟩
  have he : PointBox.calc p5_141.t = p5_141 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_142_contains : p5_142.Contains (quadraturePoint 5 142) := by
  have ht : p5_142.t.Contains (quadraturePoint 5 142) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨142,by decide⟩).scale 1 12) = p5_142.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨142,by decide⟩
  have he : PointBox.calc p5_142.t = p5_142 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_143_contains : p5_143.Contains (quadraturePoint 5 143) := by
  have ht : p5_143.t.Contains (quadraturePoint 5 143) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨143,by decide⟩).scale 1 12) = p5_143.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨143,by decide⟩
  have he : PointBox.calc p5_143.t = p5_143 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_144_contains : p5_144.Contains (quadraturePoint 5 144) := by
  have ht : p5_144.t.Contains (quadraturePoint 5 144) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨144,by decide⟩).scale 1 12) = p5_144.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨144,by decide⟩
  have he : PointBox.calc p5_144.t = p5_144 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_145_contains : p5_145.Contains (quadraturePoint 5 145) := by
  have ht : p5_145.t.Contains (quadraturePoint 5 145) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨145,by decide⟩).scale 1 12) = p5_145.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨145,by decide⟩
  have he : PointBox.calc p5_145.t = p5_145 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_146_contains : p5_146.Contains (quadraturePoint 5 146) := by
  have ht : p5_146.t.Contains (quadraturePoint 5 146) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨146,by decide⟩).scale 1 12) = p5_146.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨146,by decide⟩
  have he : PointBox.calc p5_146.t = p5_146 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_147_contains : p5_147.Contains (quadraturePoint 5 147) := by
  have ht : p5_147.t.Contains (quadraturePoint 5 147) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨147,by decide⟩).scale 1 12) = p5_147.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨147,by decide⟩
  have he : PointBox.calc p5_147.t = p5_147 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_148_contains : p5_148.Contains (quadraturePoint 5 148) := by
  have ht : p5_148.t.Contains (quadraturePoint 5 148) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨148,by decide⟩).scale 1 12) = p5_148.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨148,by decide⟩
  have he : PointBox.calc p5_148.t = p5_148 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_149_contains : p5_149.Contains (quadraturePoint 5 149) := by
  have ht : p5_149.t.Contains (quadraturePoint 5 149) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨149,by decide⟩).scale 1 12) = p5_149.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨149,by decide⟩
  have he : PointBox.calc p5_149.t = p5_149 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_150_contains : p5_150.Contains (quadraturePoint 5 150) := by
  have ht : p5_150.t.Contains (quadraturePoint 5 150) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨150,by decide⟩).scale 1 12) = p5_150.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨150,by decide⟩
  have he : PointBox.calc p5_150.t = p5_150 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_151_contains : p5_151.Contains (quadraturePoint 5 151) := by
  have ht : p5_151.t.Contains (quadraturePoint 5 151) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨151,by decide⟩).scale 1 12) = p5_151.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨151,by decide⟩
  have he : PointBox.calc p5_151.t = p5_151 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_152_contains : p5_152.Contains (quadraturePoint 5 152) := by
  have ht : p5_152.t.Contains (quadraturePoint 5 152) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨152,by decide⟩).scale 1 12) = p5_152.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨152,by decide⟩
  have he : PointBox.calc p5_152.t = p5_152 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_153_contains : p5_153.Contains (quadraturePoint 5 153) := by
  have ht : p5_153.t.Contains (quadraturePoint 5 153) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨153,by decide⟩).scale 1 12) = p5_153.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨153,by decide⟩
  have he : PointBox.calc p5_153.t = p5_153 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_154_contains : p5_154.Contains (quadraturePoint 5 154) := by
  have ht : p5_154.t.Contains (quadraturePoint 5 154) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨154,by decide⟩).scale 1 12) = p5_154.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨154,by decide⟩
  have he : PointBox.calc p5_154.t = p5_154 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_155_contains : p5_155.Contains (quadraturePoint 5 155) := by
  have ht : p5_155.t.Contains (quadraturePoint 5 155) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨155,by decide⟩).scale 1 12) = p5_155.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨155,by decide⟩
  have he : PointBox.calc p5_155.t = p5_155 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_156_contains : p5_156.Contains (quadraturePoint 5 156) := by
  have ht : p5_156.t.Contains (quadraturePoint 5 156) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨156,by decide⟩).scale 1 12) = p5_156.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨156,by decide⟩
  have he : PointBox.calc p5_156.t = p5_156 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_157_contains : p5_157.Contains (quadraturePoint 5 157) := by
  have ht : p5_157.t.Contains (quadraturePoint 5 157) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨157,by decide⟩).scale 1 12) = p5_157.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨157,by decide⟩
  have he : PointBox.calc p5_157.t = p5_157 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_158_contains : p5_158.Contains (quadraturePoint 5 158) := by
  have ht : p5_158.t.Contains (quadraturePoint 5 158) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨158,by decide⟩).scale 1 12) = p5_158.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨158,by decide⟩
  have he : PointBox.calc p5_158.t = p5_158 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_159_contains : p5_159.Contains (quadraturePoint 5 159) := by
  have ht : p5_159.t.Contains (quadraturePoint 5 159) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨159,by decide⟩).scale 1 12) = p5_159.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨159,by decide⟩
  have he : PointBox.calc p5_159.t = p5_159 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_0_contains (k : Fin 16) : (row5_0 k).Contains (quadraturePoint 5 (0+k.val)) := by
  fin_cases k
  · exact p5_0_contains
  · exact p5_1_contains
  · exact p5_2_contains
  · exact p5_3_contains
  · exact p5_4_contains
  · exact p5_5_contains
  · exact p5_6_contains
  · exact p5_7_contains
  · exact p5_8_contains
  · exact p5_9_contains
  · exact p5_10_contains
  · exact p5_11_contains
  · exact p5_12_contains
  · exact p5_13_contains
  · exact p5_14_contains
  · exact p5_15_contains
lemma row5_1_contains (k : Fin 16) : (row5_1 k).Contains (quadraturePoint 5 (16+k.val)) := by
  fin_cases k
  · exact p5_16_contains
  · exact p5_17_contains
  · exact p5_18_contains
  · exact p5_19_contains
  · exact p5_20_contains
  · exact p5_21_contains
  · exact p5_22_contains
  · exact p5_23_contains
  · exact p5_24_contains
  · exact p5_25_contains
  · exact p5_26_contains
  · exact p5_27_contains
  · exact p5_28_contains
  · exact p5_29_contains
  · exact p5_30_contains
  · exact p5_31_contains
lemma row5_2_contains (k : Fin 16) : (row5_2 k).Contains (quadraturePoint 5 (32+k.val)) := by
  fin_cases k
  · exact p5_32_contains
  · exact p5_33_contains
  · exact p5_34_contains
  · exact p5_35_contains
  · exact p5_36_contains
  · exact p5_37_contains
  · exact p5_38_contains
  · exact p5_39_contains
  · exact p5_40_contains
  · exact p5_41_contains
  · exact p5_42_contains
  · exact p5_43_contains
  · exact p5_44_contains
  · exact p5_45_contains
  · exact p5_46_contains
  · exact p5_47_contains
lemma row5_3_contains (k : Fin 16) : (row5_3 k).Contains (quadraturePoint 5 (48+k.val)) := by
  fin_cases k
  · exact p5_48_contains
  · exact p5_49_contains
  · exact p5_50_contains
  · exact p5_51_contains
  · exact p5_52_contains
  · exact p5_53_contains
  · exact p5_54_contains
  · exact p5_55_contains
  · exact p5_56_contains
  · exact p5_57_contains
  · exact p5_58_contains
  · exact p5_59_contains
  · exact p5_60_contains
  · exact p5_61_contains
  · exact p5_62_contains
  · exact p5_63_contains
lemma row5_4_contains (k : Fin 16) : (row5_4 k).Contains (quadraturePoint 5 (64+k.val)) := by
  fin_cases k
  · exact p5_64_contains
  · exact p5_65_contains
  · exact p5_66_contains
  · exact p5_67_contains
  · exact p5_68_contains
  · exact p5_69_contains
  · exact p5_70_contains
  · exact p5_71_contains
  · exact p5_72_contains
  · exact p5_73_contains
  · exact p5_74_contains
  · exact p5_75_contains
  · exact p5_76_contains
  · exact p5_77_contains
  · exact p5_78_contains
  · exact p5_79_contains
lemma row5_5_contains (k : Fin 16) : (row5_5 k).Contains (quadraturePoint 5 (80+k.val)) := by
  fin_cases k
  · exact p5_80_contains
  · exact p5_81_contains
  · exact p5_82_contains
  · exact p5_83_contains
  · exact p5_84_contains
  · exact p5_85_contains
  · exact p5_86_contains
  · exact p5_87_contains
  · exact p5_88_contains
  · exact p5_89_contains
  · exact p5_90_contains
  · exact p5_91_contains
  · exact p5_92_contains
  · exact p5_93_contains
  · exact p5_94_contains
  · exact p5_95_contains
lemma row5_6_contains (k : Fin 16) : (row5_6 k).Contains (quadraturePoint 5 (96+k.val)) := by
  fin_cases k
  · exact p5_96_contains
  · exact p5_97_contains
  · exact p5_98_contains
  · exact p5_99_contains
  · exact p5_100_contains
  · exact p5_101_contains
  · exact p5_102_contains
  · exact p5_103_contains
  · exact p5_104_contains
  · exact p5_105_contains
  · exact p5_106_contains
  · exact p5_107_contains
  · exact p5_108_contains
  · exact p5_109_contains
  · exact p5_110_contains
  · exact p5_111_contains
lemma row5_8_contains (k : Fin 16) : (row5_8 k).Contains (quadraturePoint 5 (128+k.val)) := by
  fin_cases k
  · exact p5_128_contains
  · exact p5_129_contains
  · exact p5_130_contains
  · exact p5_131_contains
  · exact p5_132_contains
  · exact p5_133_contains
  · exact p5_134_contains
  · exact p5_135_contains
  · exact p5_136_contains
  · exact p5_137_contains
  · exact p5_138_contains
  · exact p5_139_contains
  · exact p5_140_contains
  · exact p5_141_contains
  · exact p5_142_contains
  · exact p5_143_contains
lemma row5_9_contains (k : Fin 16) : (row5_9 k).Contains (quadraturePoint 5 (144+k.val)) := by
  fin_cases k
  · exact p5_144_contains
  · exact p5_145_contains
  · exact p5_146_contains
  · exact p5_147_contains
  · exact p5_148_contains
  · exact p5_149_contains
  · exact p5_150_contains
  · exact p5_151_contains
  · exact p5_152_contains
  · exact p5_153_contains
  · exact p5_154_contains
  · exact p5_155_contains
  · exact p5_156_contains
  · exact p5_157_contains
  · exact p5_158_contains
  · exact p5_159_contains
lemma row5_contains_g_oai (i k : Fin 16) : (row5 i k).Contains (quadraturePoint 5 (16*i.val+k.val)) := by
  fin_cases i
  · exact row5_0_contains k
  · exact row5_1_contains k
  · exact row5_2_contains k
  · exact row5_3_contains k
  · exact row5_4_contains k
  · exact row5_5_contains k
  · exact row5_6_contains k
  · exact row5_7_contains_g k
  · exact row5_8_contains k
  · exact row5_9_contains k
  · exact row5_10_contains_g k
  · exact row5_11_contains_g k
  · exact row5_12_contains_g k
  · exact row5_13_contains_g k
  · exact row5_14_contains_g k
  · exact row5_15_contains_g k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_contains_g_oai
