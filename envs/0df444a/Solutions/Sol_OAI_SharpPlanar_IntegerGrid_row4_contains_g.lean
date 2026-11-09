-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:34.096+00:00
-- url     : https://prove2.me/submissions/34bae3e7-4ab6-4904-bc7d-794e2ffe46fa

import Mathlib
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_14_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_7_contains_g
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

lemma p4_0_contains : p4_0.Contains (quadraturePoint 4 0) := by
  have ht : p4_0.t.Contains (quadraturePoint 4 0) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p4_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨0,by decide⟩
  have he : PointBox.calc p4_0.t = p4_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_1_contains : p4_1.Contains (quadraturePoint 4 1) := by
  have ht : p4_1.t.Contains (quadraturePoint 4 1) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p4_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨1,by decide⟩
  have he : PointBox.calc p4_1.t = p4_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_2_contains : p4_2.Contains (quadraturePoint 4 2) := by
  have ht : p4_2.t.Contains (quadraturePoint 4 2) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p4_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨2,by decide⟩
  have he : PointBox.calc p4_2.t = p4_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_3_contains : p4_3.Contains (quadraturePoint 4 3) := by
  have ht : p4_3.t.Contains (quadraturePoint 4 3) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p4_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨3,by decide⟩
  have he : PointBox.calc p4_3.t = p4_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_4_contains : p4_4.Contains (quadraturePoint 4 4) := by
  have ht : p4_4.t.Contains (quadraturePoint 4 4) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p4_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨4,by decide⟩
  have he : PointBox.calc p4_4.t = p4_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_5_contains : p4_5.Contains (quadraturePoint 4 5) := by
  have ht : p4_5.t.Contains (quadraturePoint 4 5) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p4_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨5,by decide⟩
  have he : PointBox.calc p4_5.t = p4_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_6_contains : p4_6.Contains (quadraturePoint 4 6) := by
  have ht : p4_6.t.Contains (quadraturePoint 4 6) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p4_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨6,by decide⟩
  have he : PointBox.calc p4_6.t = p4_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_7_contains : p4_7.Contains (quadraturePoint 4 7) := by
  have ht : p4_7.t.Contains (quadraturePoint 4 7) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p4_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨7,by decide⟩
  have he : PointBox.calc p4_7.t = p4_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_8_contains : p4_8.Contains (quadraturePoint 4 8) := by
  have ht : p4_8.t.Contains (quadraturePoint 4 8) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p4_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨8,by decide⟩
  have he : PointBox.calc p4_8.t = p4_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_9_contains : p4_9.Contains (quadraturePoint 4 9) := by
  have ht : p4_9.t.Contains (quadraturePoint 4 9) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p4_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨9,by decide⟩
  have he : PointBox.calc p4_9.t = p4_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_10_contains : p4_10.Contains (quadraturePoint 4 10) := by
  have ht : p4_10.t.Contains (quadraturePoint 4 10) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p4_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨10,by decide⟩
  have he : PointBox.calc p4_10.t = p4_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_11_contains : p4_11.Contains (quadraturePoint 4 11) := by
  have ht : p4_11.t.Contains (quadraturePoint 4 11) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p4_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨11,by decide⟩
  have he : PointBox.calc p4_11.t = p4_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_12_contains : p4_12.Contains (quadraturePoint 4 12) := by
  have ht : p4_12.t.Contains (quadraturePoint 4 12) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p4_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨12,by decide⟩
  have he : PointBox.calc p4_12.t = p4_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_13_contains : p4_13.Contains (quadraturePoint 4 13) := by
  have ht : p4_13.t.Contains (quadraturePoint 4 13) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p4_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨13,by decide⟩
  have he : PointBox.calc p4_13.t = p4_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_14_contains : p4_14.Contains (quadraturePoint 4 14) := by
  have ht : p4_14.t.Contains (quadraturePoint 4 14) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p4_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨14,by decide⟩
  have he : PointBox.calc p4_14.t = p4_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_15_contains : p4_15.Contains (quadraturePoint 4 15) := by
  have ht : p4_15.t.Contains (quadraturePoint 4 15) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p4_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨15,by decide⟩
  have he : PointBox.calc p4_15.t = p4_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_16_contains : p4_16.Contains (quadraturePoint 4 16) := by
  have ht : p4_16.t.Contains (quadraturePoint 4 16) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p4_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨16,by decide⟩
  have he : PointBox.calc p4_16.t = p4_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_17_contains : p4_17.Contains (quadraturePoint 4 17) := by
  have ht : p4_17.t.Contains (quadraturePoint 4 17) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p4_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨17,by decide⟩
  have he : PointBox.calc p4_17.t = p4_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_18_contains : p4_18.Contains (quadraturePoint 4 18) := by
  have ht : p4_18.t.Contains (quadraturePoint 4 18) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p4_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨18,by decide⟩
  have he : PointBox.calc p4_18.t = p4_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_19_contains : p4_19.Contains (quadraturePoint 4 19) := by
  have ht : p4_19.t.Contains (quadraturePoint 4 19) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p4_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨19,by decide⟩
  have he : PointBox.calc p4_19.t = p4_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_20_contains : p4_20.Contains (quadraturePoint 4 20) := by
  have ht : p4_20.t.Contains (quadraturePoint 4 20) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p4_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨20,by decide⟩
  have he : PointBox.calc p4_20.t = p4_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_21_contains : p4_21.Contains (quadraturePoint 4 21) := by
  have ht : p4_21.t.Contains (quadraturePoint 4 21) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p4_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨21,by decide⟩
  have he : PointBox.calc p4_21.t = p4_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_22_contains : p4_22.Contains (quadraturePoint 4 22) := by
  have ht : p4_22.t.Contains (quadraturePoint 4 22) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p4_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨22,by decide⟩
  have he : PointBox.calc p4_22.t = p4_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_23_contains : p4_23.Contains (quadraturePoint 4 23) := by
  have ht : p4_23.t.Contains (quadraturePoint 4 23) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p4_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨23,by decide⟩
  have he : PointBox.calc p4_23.t = p4_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_24_contains : p4_24.Contains (quadraturePoint 4 24) := by
  have ht : p4_24.t.Contains (quadraturePoint 4 24) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p4_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨24,by decide⟩
  have he : PointBox.calc p4_24.t = p4_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_25_contains : p4_25.Contains (quadraturePoint 4 25) := by
  have ht : p4_25.t.Contains (quadraturePoint 4 25) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p4_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨25,by decide⟩
  have he : PointBox.calc p4_25.t = p4_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_26_contains : p4_26.Contains (quadraturePoint 4 26) := by
  have ht : p4_26.t.Contains (quadraturePoint 4 26) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p4_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨26,by decide⟩
  have he : PointBox.calc p4_26.t = p4_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_27_contains : p4_27.Contains (quadraturePoint 4 27) := by
  have ht : p4_27.t.Contains (quadraturePoint 4 27) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p4_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨27,by decide⟩
  have he : PointBox.calc p4_27.t = p4_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_28_contains : p4_28.Contains (quadraturePoint 4 28) := by
  have ht : p4_28.t.Contains (quadraturePoint 4 28) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p4_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨28,by decide⟩
  have he : PointBox.calc p4_28.t = p4_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_29_contains : p4_29.Contains (quadraturePoint 4 29) := by
  have ht : p4_29.t.Contains (quadraturePoint 4 29) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p4_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨29,by decide⟩
  have he : PointBox.calc p4_29.t = p4_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_30_contains : p4_30.Contains (quadraturePoint 4 30) := by
  have ht : p4_30.t.Contains (quadraturePoint 4 30) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p4_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨30,by decide⟩
  have he : PointBox.calc p4_30.t = p4_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_31_contains : p4_31.Contains (quadraturePoint 4 31) := by
  have ht : p4_31.t.Contains (quadraturePoint 4 31) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p4_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨31,by decide⟩
  have he : PointBox.calc p4_31.t = p4_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_32_contains : p4_32.Contains (quadraturePoint 4 32) := by
  have ht : p4_32.t.Contains (quadraturePoint 4 32) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨32,by decide⟩).scale 1 12) = p4_32.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨32,by decide⟩
  have he : PointBox.calc p4_32.t = p4_32 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_33_contains : p4_33.Contains (quadraturePoint 4 33) := by
  have ht : p4_33.t.Contains (quadraturePoint 4 33) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨33,by decide⟩).scale 1 12) = p4_33.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨33,by decide⟩
  have he : PointBox.calc p4_33.t = p4_33 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_34_contains : p4_34.Contains (quadraturePoint 4 34) := by
  have ht : p4_34.t.Contains (quadraturePoint 4 34) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨34,by decide⟩).scale 1 12) = p4_34.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨34,by decide⟩
  have he : PointBox.calc p4_34.t = p4_34 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_35_contains : p4_35.Contains (quadraturePoint 4 35) := by
  have ht : p4_35.t.Contains (quadraturePoint 4 35) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨35,by decide⟩).scale 1 12) = p4_35.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨35,by decide⟩
  have he : PointBox.calc p4_35.t = p4_35 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_36_contains : p4_36.Contains (quadraturePoint 4 36) := by
  have ht : p4_36.t.Contains (quadraturePoint 4 36) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨36,by decide⟩).scale 1 12) = p4_36.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨36,by decide⟩
  have he : PointBox.calc p4_36.t = p4_36 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_37_contains : p4_37.Contains (quadraturePoint 4 37) := by
  have ht : p4_37.t.Contains (quadraturePoint 4 37) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨37,by decide⟩).scale 1 12) = p4_37.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨37,by decide⟩
  have he : PointBox.calc p4_37.t = p4_37 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_38_contains : p4_38.Contains (quadraturePoint 4 38) := by
  have ht : p4_38.t.Contains (quadraturePoint 4 38) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨38,by decide⟩).scale 1 12) = p4_38.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨38,by decide⟩
  have he : PointBox.calc p4_38.t = p4_38 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_39_contains : p4_39.Contains (quadraturePoint 4 39) := by
  have ht : p4_39.t.Contains (quadraturePoint 4 39) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨39,by decide⟩).scale 1 12) = p4_39.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨39,by decide⟩
  have he : PointBox.calc p4_39.t = p4_39 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_40_contains : p4_40.Contains (quadraturePoint 4 40) := by
  have ht : p4_40.t.Contains (quadraturePoint 4 40) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨40,by decide⟩).scale 1 12) = p4_40.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨40,by decide⟩
  have he : PointBox.calc p4_40.t = p4_40 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_41_contains : p4_41.Contains (quadraturePoint 4 41) := by
  have ht : p4_41.t.Contains (quadraturePoint 4 41) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨41,by decide⟩).scale 1 12) = p4_41.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨41,by decide⟩
  have he : PointBox.calc p4_41.t = p4_41 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_42_contains : p4_42.Contains (quadraturePoint 4 42) := by
  have ht : p4_42.t.Contains (quadraturePoint 4 42) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨42,by decide⟩).scale 1 12) = p4_42.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨42,by decide⟩
  have he : PointBox.calc p4_42.t = p4_42 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_43_contains : p4_43.Contains (quadraturePoint 4 43) := by
  have ht : p4_43.t.Contains (quadraturePoint 4 43) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨43,by decide⟩).scale 1 12) = p4_43.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨43,by decide⟩
  have he : PointBox.calc p4_43.t = p4_43 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_44_contains : p4_44.Contains (quadraturePoint 4 44) := by
  have ht : p4_44.t.Contains (quadraturePoint 4 44) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨44,by decide⟩).scale 1 12) = p4_44.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨44,by decide⟩
  have he : PointBox.calc p4_44.t = p4_44 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_45_contains : p4_45.Contains (quadraturePoint 4 45) := by
  have ht : p4_45.t.Contains (quadraturePoint 4 45) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨45,by decide⟩).scale 1 12) = p4_45.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨45,by decide⟩
  have he : PointBox.calc p4_45.t = p4_45 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_46_contains : p4_46.Contains (quadraturePoint 4 46) := by
  have ht : p4_46.t.Contains (quadraturePoint 4 46) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨46,by decide⟩).scale 1 12) = p4_46.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨46,by decide⟩
  have he : PointBox.calc p4_46.t = p4_46 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_47_contains : p4_47.Contains (quadraturePoint 4 47) := by
  have ht : p4_47.t.Contains (quadraturePoint 4 47) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨47,by decide⟩).scale 1 12) = p4_47.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨47,by decide⟩
  have he : PointBox.calc p4_47.t = p4_47 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_48_contains : p4_48.Contains (quadraturePoint 4 48) := by
  have ht : p4_48.t.Contains (quadraturePoint 4 48) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p4_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨48,by decide⟩
  have he : PointBox.calc p4_48.t = p4_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_49_contains : p4_49.Contains (quadraturePoint 4 49) := by
  have ht : p4_49.t.Contains (quadraturePoint 4 49) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p4_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨49,by decide⟩
  have he : PointBox.calc p4_49.t = p4_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_50_contains : p4_50.Contains (quadraturePoint 4 50) := by
  have ht : p4_50.t.Contains (quadraturePoint 4 50) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p4_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨50,by decide⟩
  have he : PointBox.calc p4_50.t = p4_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_51_contains : p4_51.Contains (quadraturePoint 4 51) := by
  have ht : p4_51.t.Contains (quadraturePoint 4 51) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p4_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨51,by decide⟩
  have he : PointBox.calc p4_51.t = p4_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_52_contains : p4_52.Contains (quadraturePoint 4 52) := by
  have ht : p4_52.t.Contains (quadraturePoint 4 52) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p4_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨52,by decide⟩
  have he : PointBox.calc p4_52.t = p4_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_53_contains : p4_53.Contains (quadraturePoint 4 53) := by
  have ht : p4_53.t.Contains (quadraturePoint 4 53) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p4_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨53,by decide⟩
  have he : PointBox.calc p4_53.t = p4_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_54_contains : p4_54.Contains (quadraturePoint 4 54) := by
  have ht : p4_54.t.Contains (quadraturePoint 4 54) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p4_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨54,by decide⟩
  have he : PointBox.calc p4_54.t = p4_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_55_contains : p4_55.Contains (quadraturePoint 4 55) := by
  have ht : p4_55.t.Contains (quadraturePoint 4 55) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p4_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨55,by decide⟩
  have he : PointBox.calc p4_55.t = p4_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_56_contains : p4_56.Contains (quadraturePoint 4 56) := by
  have ht : p4_56.t.Contains (quadraturePoint 4 56) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p4_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨56,by decide⟩
  have he : PointBox.calc p4_56.t = p4_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_57_contains : p4_57.Contains (quadraturePoint 4 57) := by
  have ht : p4_57.t.Contains (quadraturePoint 4 57) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p4_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨57,by decide⟩
  have he : PointBox.calc p4_57.t = p4_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_58_contains : p4_58.Contains (quadraturePoint 4 58) := by
  have ht : p4_58.t.Contains (quadraturePoint 4 58) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p4_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨58,by decide⟩
  have he : PointBox.calc p4_58.t = p4_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_59_contains : p4_59.Contains (quadraturePoint 4 59) := by
  have ht : p4_59.t.Contains (quadraturePoint 4 59) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p4_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨59,by decide⟩
  have he : PointBox.calc p4_59.t = p4_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_60_contains : p4_60.Contains (quadraturePoint 4 60) := by
  have ht : p4_60.t.Contains (quadraturePoint 4 60) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p4_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨60,by decide⟩
  have he : PointBox.calc p4_60.t = p4_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_61_contains : p4_61.Contains (quadraturePoint 4 61) := by
  have ht : p4_61.t.Contains (quadraturePoint 4 61) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p4_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨61,by decide⟩
  have he : PointBox.calc p4_61.t = p4_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_62_contains : p4_62.Contains (quadraturePoint 4 62) := by
  have ht : p4_62.t.Contains (quadraturePoint 4 62) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p4_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨62,by decide⟩
  have he : PointBox.calc p4_62.t = p4_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_63_contains : p4_63.Contains (quadraturePoint 4 63) := by
  have ht : p4_63.t.Contains (quadraturePoint 4 63) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p4_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨63,by decide⟩
  have he : PointBox.calc p4_63.t = p4_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_64_contains : p4_64.Contains (quadraturePoint 4 64) := by
  have ht : p4_64.t.Contains (quadraturePoint 4 64) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p4_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨64,by decide⟩
  have he : PointBox.calc p4_64.t = p4_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_65_contains : p4_65.Contains (quadraturePoint 4 65) := by
  have ht : p4_65.t.Contains (quadraturePoint 4 65) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p4_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨65,by decide⟩
  have he : PointBox.calc p4_65.t = p4_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_66_contains : p4_66.Contains (quadraturePoint 4 66) := by
  have ht : p4_66.t.Contains (quadraturePoint 4 66) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p4_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨66,by decide⟩
  have he : PointBox.calc p4_66.t = p4_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_67_contains : p4_67.Contains (quadraturePoint 4 67) := by
  have ht : p4_67.t.Contains (quadraturePoint 4 67) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p4_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨67,by decide⟩
  have he : PointBox.calc p4_67.t = p4_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_68_contains : p4_68.Contains (quadraturePoint 4 68) := by
  have ht : p4_68.t.Contains (quadraturePoint 4 68) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p4_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨68,by decide⟩
  have he : PointBox.calc p4_68.t = p4_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_69_contains : p4_69.Contains (quadraturePoint 4 69) := by
  have ht : p4_69.t.Contains (quadraturePoint 4 69) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p4_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨69,by decide⟩
  have he : PointBox.calc p4_69.t = p4_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_70_contains : p4_70.Contains (quadraturePoint 4 70) := by
  have ht : p4_70.t.Contains (quadraturePoint 4 70) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p4_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨70,by decide⟩
  have he : PointBox.calc p4_70.t = p4_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_71_contains : p4_71.Contains (quadraturePoint 4 71) := by
  have ht : p4_71.t.Contains (quadraturePoint 4 71) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p4_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨71,by decide⟩
  have he : PointBox.calc p4_71.t = p4_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_72_contains : p4_72.Contains (quadraturePoint 4 72) := by
  have ht : p4_72.t.Contains (quadraturePoint 4 72) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p4_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨72,by decide⟩
  have he : PointBox.calc p4_72.t = p4_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_73_contains : p4_73.Contains (quadraturePoint 4 73) := by
  have ht : p4_73.t.Contains (quadraturePoint 4 73) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p4_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨73,by decide⟩
  have he : PointBox.calc p4_73.t = p4_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_74_contains : p4_74.Contains (quadraturePoint 4 74) := by
  have ht : p4_74.t.Contains (quadraturePoint 4 74) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p4_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨74,by decide⟩
  have he : PointBox.calc p4_74.t = p4_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_75_contains : p4_75.Contains (quadraturePoint 4 75) := by
  have ht : p4_75.t.Contains (quadraturePoint 4 75) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p4_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨75,by decide⟩
  have he : PointBox.calc p4_75.t = p4_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_76_contains : p4_76.Contains (quadraturePoint 4 76) := by
  have ht : p4_76.t.Contains (quadraturePoint 4 76) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p4_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨76,by decide⟩
  have he : PointBox.calc p4_76.t = p4_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_77_contains : p4_77.Contains (quadraturePoint 4 77) := by
  have ht : p4_77.t.Contains (quadraturePoint 4 77) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p4_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨77,by decide⟩
  have he : PointBox.calc p4_77.t = p4_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_78_contains : p4_78.Contains (quadraturePoint 4 78) := by
  have ht : p4_78.t.Contains (quadraturePoint 4 78) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p4_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨78,by decide⟩
  have he : PointBox.calc p4_78.t = p4_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_79_contains : p4_79.Contains (quadraturePoint 4 79) := by
  have ht : p4_79.t.Contains (quadraturePoint 4 79) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p4_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨79,by decide⟩
  have he : PointBox.calc p4_79.t = p4_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_80_contains : p4_80.Contains (quadraturePoint 4 80) := by
  have ht : p4_80.t.Contains (quadraturePoint 4 80) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p4_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨80,by decide⟩
  have he : PointBox.calc p4_80.t = p4_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_81_contains : p4_81.Contains (quadraturePoint 4 81) := by
  have ht : p4_81.t.Contains (quadraturePoint 4 81) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p4_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨81,by decide⟩
  have he : PointBox.calc p4_81.t = p4_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_82_contains : p4_82.Contains (quadraturePoint 4 82) := by
  have ht : p4_82.t.Contains (quadraturePoint 4 82) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p4_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨82,by decide⟩
  have he : PointBox.calc p4_82.t = p4_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_83_contains : p4_83.Contains (quadraturePoint 4 83) := by
  have ht : p4_83.t.Contains (quadraturePoint 4 83) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p4_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨83,by decide⟩
  have he : PointBox.calc p4_83.t = p4_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_84_contains : p4_84.Contains (quadraturePoint 4 84) := by
  have ht : p4_84.t.Contains (quadraturePoint 4 84) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p4_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨84,by decide⟩
  have he : PointBox.calc p4_84.t = p4_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_85_contains : p4_85.Contains (quadraturePoint 4 85) := by
  have ht : p4_85.t.Contains (quadraturePoint 4 85) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p4_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨85,by decide⟩
  have he : PointBox.calc p4_85.t = p4_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_86_contains : p4_86.Contains (quadraturePoint 4 86) := by
  have ht : p4_86.t.Contains (quadraturePoint 4 86) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p4_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨86,by decide⟩
  have he : PointBox.calc p4_86.t = p4_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_87_contains : p4_87.Contains (quadraturePoint 4 87) := by
  have ht : p4_87.t.Contains (quadraturePoint 4 87) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p4_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨87,by decide⟩
  have he : PointBox.calc p4_87.t = p4_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_88_contains : p4_88.Contains (quadraturePoint 4 88) := by
  have ht : p4_88.t.Contains (quadraturePoint 4 88) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p4_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨88,by decide⟩
  have he : PointBox.calc p4_88.t = p4_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_89_contains : p4_89.Contains (quadraturePoint 4 89) := by
  have ht : p4_89.t.Contains (quadraturePoint 4 89) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p4_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨89,by decide⟩
  have he : PointBox.calc p4_89.t = p4_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_90_contains : p4_90.Contains (quadraturePoint 4 90) := by
  have ht : p4_90.t.Contains (quadraturePoint 4 90) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p4_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨90,by decide⟩
  have he : PointBox.calc p4_90.t = p4_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_91_contains : p4_91.Contains (quadraturePoint 4 91) := by
  have ht : p4_91.t.Contains (quadraturePoint 4 91) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p4_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨91,by decide⟩
  have he : PointBox.calc p4_91.t = p4_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_92_contains : p4_92.Contains (quadraturePoint 4 92) := by
  have ht : p4_92.t.Contains (quadraturePoint 4 92) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p4_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨92,by decide⟩
  have he : PointBox.calc p4_92.t = p4_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_93_contains : p4_93.Contains (quadraturePoint 4 93) := by
  have ht : p4_93.t.Contains (quadraturePoint 4 93) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p4_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨93,by decide⟩
  have he : PointBox.calc p4_93.t = p4_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_94_contains : p4_94.Contains (quadraturePoint 4 94) := by
  have ht : p4_94.t.Contains (quadraturePoint 4 94) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p4_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨94,by decide⟩
  have he : PointBox.calc p4_94.t = p4_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_95_contains : p4_95.Contains (quadraturePoint 4 95) := by
  have ht : p4_95.t.Contains (quadraturePoint 4 95) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p4_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨95,by decide⟩
  have he : PointBox.calc p4_95.t = p4_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_96_contains : p4_96.Contains (quadraturePoint 4 96) := by
  have ht : p4_96.t.Contains (quadraturePoint 4 96) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨96,by decide⟩).scale 1 12) = p4_96.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨96,by decide⟩
  have he : PointBox.calc p4_96.t = p4_96 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_97_contains : p4_97.Contains (quadraturePoint 4 97) := by
  have ht : p4_97.t.Contains (quadraturePoint 4 97) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p4_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨97,by decide⟩
  have he : PointBox.calc p4_97.t = p4_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_98_contains : p4_98.Contains (quadraturePoint 4 98) := by
  have ht : p4_98.t.Contains (quadraturePoint 4 98) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨98,by decide⟩).scale 1 12) = p4_98.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨98,by decide⟩
  have he : PointBox.calc p4_98.t = p4_98 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_99_contains : p4_99.Contains (quadraturePoint 4 99) := by
  have ht : p4_99.t.Contains (quadraturePoint 4 99) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨99,by decide⟩).scale 1 12) = p4_99.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨99,by decide⟩
  have he : PointBox.calc p4_99.t = p4_99 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_100_contains : p4_100.Contains (quadraturePoint 4 100) := by
  have ht : p4_100.t.Contains (quadraturePoint 4 100) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨100,by decide⟩).scale 1 12) = p4_100.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨100,by decide⟩
  have he : PointBox.calc p4_100.t = p4_100 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_101_contains : p4_101.Contains (quadraturePoint 4 101) := by
  have ht : p4_101.t.Contains (quadraturePoint 4 101) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨101,by decide⟩).scale 1 12) = p4_101.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨101,by decide⟩
  have he : PointBox.calc p4_101.t = p4_101 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_102_contains : p4_102.Contains (quadraturePoint 4 102) := by
  have ht : p4_102.t.Contains (quadraturePoint 4 102) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨102,by decide⟩).scale 1 12) = p4_102.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨102,by decide⟩
  have he : PointBox.calc p4_102.t = p4_102 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_103_contains : p4_103.Contains (quadraturePoint 4 103) := by
  have ht : p4_103.t.Contains (quadraturePoint 4 103) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨103,by decide⟩).scale 1 12) = p4_103.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨103,by decide⟩
  have he : PointBox.calc p4_103.t = p4_103 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_104_contains : p4_104.Contains (quadraturePoint 4 104) := by
  have ht : p4_104.t.Contains (quadraturePoint 4 104) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨104,by decide⟩).scale 1 12) = p4_104.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨104,by decide⟩
  have he : PointBox.calc p4_104.t = p4_104 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_105_contains : p4_105.Contains (quadraturePoint 4 105) := by
  have ht : p4_105.t.Contains (quadraturePoint 4 105) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨105,by decide⟩).scale 1 12) = p4_105.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨105,by decide⟩
  have he : PointBox.calc p4_105.t = p4_105 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_106_contains : p4_106.Contains (quadraturePoint 4 106) := by
  have ht : p4_106.t.Contains (quadraturePoint 4 106) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨106,by decide⟩).scale 1 12) = p4_106.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨106,by decide⟩
  have he : PointBox.calc p4_106.t = p4_106 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_107_contains : p4_107.Contains (quadraturePoint 4 107) := by
  have ht : p4_107.t.Contains (quadraturePoint 4 107) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨107,by decide⟩).scale 1 12) = p4_107.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨107,by decide⟩
  have he : PointBox.calc p4_107.t = p4_107 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_108_contains : p4_108.Contains (quadraturePoint 4 108) := by
  have ht : p4_108.t.Contains (quadraturePoint 4 108) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨108,by decide⟩).scale 1 12) = p4_108.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨108,by decide⟩
  have he : PointBox.calc p4_108.t = p4_108 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_109_contains : p4_109.Contains (quadraturePoint 4 109) := by
  have ht : p4_109.t.Contains (quadraturePoint 4 109) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨109,by decide⟩).scale 1 12) = p4_109.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨109,by decide⟩
  have he : PointBox.calc p4_109.t = p4_109 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_110_contains : p4_110.Contains (quadraturePoint 4 110) := by
  have ht : p4_110.t.Contains (quadraturePoint 4 110) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨110,by decide⟩).scale 1 12) = p4_110.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨110,by decide⟩
  have he : PointBox.calc p4_110.t = p4_110 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_111_contains : p4_111.Contains (quadraturePoint 4 111) := by
  have ht : p4_111.t.Contains (quadraturePoint 4 111) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨111,by decide⟩).scale 1 12) = p4_111.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨111,by decide⟩
  have he : PointBox.calc p4_111.t = p4_111 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_128_contains : p4_128.Contains (quadraturePoint 4 128) := by
  have ht : p4_128.t.Contains (quadraturePoint 4 128) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨128,by decide⟩).scale 1 12) = p4_128.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨128,by decide⟩
  have he : PointBox.calc p4_128.t = p4_128 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_129_contains : p4_129.Contains (quadraturePoint 4 129) := by
  have ht : p4_129.t.Contains (quadraturePoint 4 129) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨129,by decide⟩).scale 1 12) = p4_129.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨129,by decide⟩
  have he : PointBox.calc p4_129.t = p4_129 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_130_contains : p4_130.Contains (quadraturePoint 4 130) := by
  have ht : p4_130.t.Contains (quadraturePoint 4 130) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨130,by decide⟩).scale 1 12) = p4_130.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨130,by decide⟩
  have he : PointBox.calc p4_130.t = p4_130 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_131_contains : p4_131.Contains (quadraturePoint 4 131) := by
  have ht : p4_131.t.Contains (quadraturePoint 4 131) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨131,by decide⟩).scale 1 12) = p4_131.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨131,by decide⟩
  have he : PointBox.calc p4_131.t = p4_131 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_132_contains : p4_132.Contains (quadraturePoint 4 132) := by
  have ht : p4_132.t.Contains (quadraturePoint 4 132) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨132,by decide⟩).scale 1 12) = p4_132.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨132,by decide⟩
  have he : PointBox.calc p4_132.t = p4_132 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_133_contains : p4_133.Contains (quadraturePoint 4 133) := by
  have ht : p4_133.t.Contains (quadraturePoint 4 133) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨133,by decide⟩).scale 1 12) = p4_133.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨133,by decide⟩
  have he : PointBox.calc p4_133.t = p4_133 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_134_contains : p4_134.Contains (quadraturePoint 4 134) := by
  have ht : p4_134.t.Contains (quadraturePoint 4 134) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨134,by decide⟩).scale 1 12) = p4_134.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨134,by decide⟩
  have he : PointBox.calc p4_134.t = p4_134 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_135_contains : p4_135.Contains (quadraturePoint 4 135) := by
  have ht : p4_135.t.Contains (quadraturePoint 4 135) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨135,by decide⟩).scale 1 12) = p4_135.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨135,by decide⟩
  have he : PointBox.calc p4_135.t = p4_135 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_136_contains : p4_136.Contains (quadraturePoint 4 136) := by
  have ht : p4_136.t.Contains (quadraturePoint 4 136) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨136,by decide⟩).scale 1 12) = p4_136.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨136,by decide⟩
  have he : PointBox.calc p4_136.t = p4_136 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_137_contains : p4_137.Contains (quadraturePoint 4 137) := by
  have ht : p4_137.t.Contains (quadraturePoint 4 137) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨137,by decide⟩).scale 1 12) = p4_137.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨137,by decide⟩
  have he : PointBox.calc p4_137.t = p4_137 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_138_contains : p4_138.Contains (quadraturePoint 4 138) := by
  have ht : p4_138.t.Contains (quadraturePoint 4 138) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨138,by decide⟩).scale 1 12) = p4_138.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨138,by decide⟩
  have he : PointBox.calc p4_138.t = p4_138 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_139_contains : p4_139.Contains (quadraturePoint 4 139) := by
  have ht : p4_139.t.Contains (quadraturePoint 4 139) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨139,by decide⟩).scale 1 12) = p4_139.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨139,by decide⟩
  have he : PointBox.calc p4_139.t = p4_139 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_140_contains : p4_140.Contains (quadraturePoint 4 140) := by
  have ht : p4_140.t.Contains (quadraturePoint 4 140) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨140,by decide⟩).scale 1 12) = p4_140.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨140,by decide⟩
  have he : PointBox.calc p4_140.t = p4_140 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_141_contains : p4_141.Contains (quadraturePoint 4 141) := by
  have ht : p4_141.t.Contains (quadraturePoint 4 141) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨141,by decide⟩).scale 1 12) = p4_141.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨141,by decide⟩
  have he : PointBox.calc p4_141.t = p4_141 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_142_contains : p4_142.Contains (quadraturePoint 4 142) := by
  have ht : p4_142.t.Contains (quadraturePoint 4 142) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨142,by decide⟩).scale 1 12) = p4_142.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨142,by decide⟩
  have he : PointBox.calc p4_142.t = p4_142 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_143_contains : p4_143.Contains (quadraturePoint 4 143) := by
  have ht : p4_143.t.Contains (quadraturePoint 4 143) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨143,by decide⟩).scale 1 12) = p4_143.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨143,by decide⟩
  have he : PointBox.calc p4_143.t = p4_143 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_144_contains : p4_144.Contains (quadraturePoint 4 144) := by
  have ht : p4_144.t.Contains (quadraturePoint 4 144) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨144,by decide⟩).scale 1 12) = p4_144.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨144,by decide⟩
  have he : PointBox.calc p4_144.t = p4_144 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_145_contains : p4_145.Contains (quadraturePoint 4 145) := by
  have ht : p4_145.t.Contains (quadraturePoint 4 145) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨145,by decide⟩).scale 1 12) = p4_145.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨145,by decide⟩
  have he : PointBox.calc p4_145.t = p4_145 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_146_contains : p4_146.Contains (quadraturePoint 4 146) := by
  have ht : p4_146.t.Contains (quadraturePoint 4 146) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨146,by decide⟩).scale 1 12) = p4_146.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨146,by decide⟩
  have he : PointBox.calc p4_146.t = p4_146 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_147_contains : p4_147.Contains (quadraturePoint 4 147) := by
  have ht : p4_147.t.Contains (quadraturePoint 4 147) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨147,by decide⟩).scale 1 12) = p4_147.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨147,by decide⟩
  have he : PointBox.calc p4_147.t = p4_147 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_148_contains : p4_148.Contains (quadraturePoint 4 148) := by
  have ht : p4_148.t.Contains (quadraturePoint 4 148) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨148,by decide⟩).scale 1 12) = p4_148.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨148,by decide⟩
  have he : PointBox.calc p4_148.t = p4_148 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_149_contains : p4_149.Contains (quadraturePoint 4 149) := by
  have ht : p4_149.t.Contains (quadraturePoint 4 149) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨149,by decide⟩).scale 1 12) = p4_149.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨149,by decide⟩
  have he : PointBox.calc p4_149.t = p4_149 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_150_contains : p4_150.Contains (quadraturePoint 4 150) := by
  have ht : p4_150.t.Contains (quadraturePoint 4 150) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨150,by decide⟩).scale 1 12) = p4_150.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨150,by decide⟩
  have he : PointBox.calc p4_150.t = p4_150 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_151_contains : p4_151.Contains (quadraturePoint 4 151) := by
  have ht : p4_151.t.Contains (quadraturePoint 4 151) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨151,by decide⟩).scale 1 12) = p4_151.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨151,by decide⟩
  have he : PointBox.calc p4_151.t = p4_151 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_152_contains : p4_152.Contains (quadraturePoint 4 152) := by
  have ht : p4_152.t.Contains (quadraturePoint 4 152) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨152,by decide⟩).scale 1 12) = p4_152.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨152,by decide⟩
  have he : PointBox.calc p4_152.t = p4_152 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_153_contains : p4_153.Contains (quadraturePoint 4 153) := by
  have ht : p4_153.t.Contains (quadraturePoint 4 153) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨153,by decide⟩).scale 1 12) = p4_153.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨153,by decide⟩
  have he : PointBox.calc p4_153.t = p4_153 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_154_contains : p4_154.Contains (quadraturePoint 4 154) := by
  have ht : p4_154.t.Contains (quadraturePoint 4 154) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨154,by decide⟩).scale 1 12) = p4_154.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨154,by decide⟩
  have he : PointBox.calc p4_154.t = p4_154 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_155_contains : p4_155.Contains (quadraturePoint 4 155) := by
  have ht : p4_155.t.Contains (quadraturePoint 4 155) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨155,by decide⟩).scale 1 12) = p4_155.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨155,by decide⟩
  have he : PointBox.calc p4_155.t = p4_155 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_156_contains : p4_156.Contains (quadraturePoint 4 156) := by
  have ht : p4_156.t.Contains (quadraturePoint 4 156) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨156,by decide⟩).scale 1 12) = p4_156.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨156,by decide⟩
  have he : PointBox.calc p4_156.t = p4_156 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_157_contains : p4_157.Contains (quadraturePoint 4 157) := by
  have ht : p4_157.t.Contains (quadraturePoint 4 157) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨157,by decide⟩).scale 1 12) = p4_157.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨157,by decide⟩
  have he : PointBox.calc p4_157.t = p4_157 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_158_contains : p4_158.Contains (quadraturePoint 4 158) := by
  have ht : p4_158.t.Contains (quadraturePoint 4 158) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨158,by decide⟩).scale 1 12) = p4_158.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨158,by decide⟩
  have he : PointBox.calc p4_158.t = p4_158 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p4_159_contains : p4_159.Contains (quadraturePoint 4 159) := by
  have ht : p4_159.t.Contains (quadraturePoint 4 159) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨159,by decide⟩).scale 1 12) = p4_159.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨159,by decide⟩
  have he : PointBox.calc p4_159.t = p4_159 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row4_0_contains (k : Fin 16) : (row4_0 k).Contains (quadraturePoint 4 (0+k.val)) := by
  fin_cases k
  · exact p4_0_contains
  · exact p4_1_contains
  · exact p4_2_contains
  · exact p4_3_contains
  · exact p4_4_contains
  · exact p4_5_contains
  · exact p4_6_contains
  · exact p4_7_contains
  · exact p4_8_contains
  · exact p4_9_contains
  · exact p4_10_contains
  · exact p4_11_contains
  · exact p4_12_contains
  · exact p4_13_contains
  · exact p4_14_contains
  · exact p4_15_contains
lemma row4_1_contains (k : Fin 16) : (row4_1 k).Contains (quadraturePoint 4 (16+k.val)) := by
  fin_cases k
  · exact p4_16_contains
  · exact p4_17_contains
  · exact p4_18_contains
  · exact p4_19_contains
  · exact p4_20_contains
  · exact p4_21_contains
  · exact p4_22_contains
  · exact p4_23_contains
  · exact p4_24_contains
  · exact p4_25_contains
  · exact p4_26_contains
  · exact p4_27_contains
  · exact p4_28_contains
  · exact p4_29_contains
  · exact p4_30_contains
  · exact p4_31_contains
lemma row4_2_contains (k : Fin 16) : (row4_2 k).Contains (quadraturePoint 4 (32+k.val)) := by
  fin_cases k
  · exact p4_32_contains
  · exact p4_33_contains
  · exact p4_34_contains
  · exact p4_35_contains
  · exact p4_36_contains
  · exact p4_37_contains
  · exact p4_38_contains
  · exact p4_39_contains
  · exact p4_40_contains
  · exact p4_41_contains
  · exact p4_42_contains
  · exact p4_43_contains
  · exact p4_44_contains
  · exact p4_45_contains
  · exact p4_46_contains
  · exact p4_47_contains
lemma row4_3_contains (k : Fin 16) : (row4_3 k).Contains (quadraturePoint 4 (48+k.val)) := by
  fin_cases k
  · exact p4_48_contains
  · exact p4_49_contains
  · exact p4_50_contains
  · exact p4_51_contains
  · exact p4_52_contains
  · exact p4_53_contains
  · exact p4_54_contains
  · exact p4_55_contains
  · exact p4_56_contains
  · exact p4_57_contains
  · exact p4_58_contains
  · exact p4_59_contains
  · exact p4_60_contains
  · exact p4_61_contains
  · exact p4_62_contains
  · exact p4_63_contains
lemma row4_4_contains (k : Fin 16) : (row4_4 k).Contains (quadraturePoint 4 (64+k.val)) := by
  fin_cases k
  · exact p4_64_contains
  · exact p4_65_contains
  · exact p4_66_contains
  · exact p4_67_contains
  · exact p4_68_contains
  · exact p4_69_contains
  · exact p4_70_contains
  · exact p4_71_contains
  · exact p4_72_contains
  · exact p4_73_contains
  · exact p4_74_contains
  · exact p4_75_contains
  · exact p4_76_contains
  · exact p4_77_contains
  · exact p4_78_contains
  · exact p4_79_contains
lemma row4_5_contains (k : Fin 16) : (row4_5 k).Contains (quadraturePoint 4 (80+k.val)) := by
  fin_cases k
  · exact p4_80_contains
  · exact p4_81_contains
  · exact p4_82_contains
  · exact p4_83_contains
  · exact p4_84_contains
  · exact p4_85_contains
  · exact p4_86_contains
  · exact p4_87_contains
  · exact p4_88_contains
  · exact p4_89_contains
  · exact p4_90_contains
  · exact p4_91_contains
  · exact p4_92_contains
  · exact p4_93_contains
  · exact p4_94_contains
  · exact p4_95_contains
lemma row4_6_contains (k : Fin 16) : (row4_6 k).Contains (quadraturePoint 4 (96+k.val)) := by
  fin_cases k
  · exact p4_96_contains
  · exact p4_97_contains
  · exact p4_98_contains
  · exact p4_99_contains
  · exact p4_100_contains
  · exact p4_101_contains
  · exact p4_102_contains
  · exact p4_103_contains
  · exact p4_104_contains
  · exact p4_105_contains
  · exact p4_106_contains
  · exact p4_107_contains
  · exact p4_108_contains
  · exact p4_109_contains
  · exact p4_110_contains
  · exact p4_111_contains
lemma row4_8_contains (k : Fin 16) : (row4_8 k).Contains (quadraturePoint 4 (128+k.val)) := by
  fin_cases k
  · exact p4_128_contains
  · exact p4_129_contains
  · exact p4_130_contains
  · exact p4_131_contains
  · exact p4_132_contains
  · exact p4_133_contains
  · exact p4_134_contains
  · exact p4_135_contains
  · exact p4_136_contains
  · exact p4_137_contains
  · exact p4_138_contains
  · exact p4_139_contains
  · exact p4_140_contains
  · exact p4_141_contains
  · exact p4_142_contains
  · exact p4_143_contains
lemma row4_9_contains (k : Fin 16) : (row4_9 k).Contains (quadraturePoint 4 (144+k.val)) := by
  fin_cases k
  · exact p4_144_contains
  · exact p4_145_contains
  · exact p4_146_contains
  · exact p4_147_contains
  · exact p4_148_contains
  · exact p4_149_contains
  · exact p4_150_contains
  · exact p4_151_contains
  · exact p4_152_contains
  · exact p4_153_contains
  · exact p4_154_contains
  · exact p4_155_contains
  · exact p4_156_contains
  · exact p4_157_contains
  · exact p4_158_contains
  · exact p4_159_contains
lemma row4_contains_g_oai (i k : Fin 16) : (row4 i k).Contains (quadraturePoint 4 (16*i.val+k.val)) := by
  fin_cases i
  · exact row4_0_contains k
  · exact row4_1_contains k
  · exact row4_2_contains k
  · exact row4_3_contains k
  · exact row4_4_contains k
  · exact row4_5_contains k
  · exact row4_6_contains k
  · exact row4_7_contains_g k
  · exact row4_8_contains k
  · exact row4_9_contains k
  · exact row4_10_contains_g k
  · exact row4_11_contains_g k
  · exact row4_12_contains_g k
  · exact row4_13_contains_g k
  · exact row4_14_contains_g k
  · exact row4_15_contains_g k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row4_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row4_contains_g_oai
