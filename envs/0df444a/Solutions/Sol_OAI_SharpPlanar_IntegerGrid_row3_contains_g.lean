-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:50.744204+00:00
-- url     : https://prove2.me/submissions/63646fc7-4f62-4746-ad11-0e1f2c154455

import Mathlib
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_9_contains_g
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

lemma p3_0_contains : p3_0.Contains (quadraturePoint 3 0) := by
  have ht : p3_0.t.Contains (quadraturePoint 3 0) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p3_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨0,by decide⟩
  have he : PointBox.calc p3_0.t = p3_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_1_contains : p3_1.Contains (quadraturePoint 3 1) := by
  have ht : p3_1.t.Contains (quadraturePoint 3 1) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p3_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨1,by decide⟩
  have he : PointBox.calc p3_1.t = p3_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_2_contains : p3_2.Contains (quadraturePoint 3 2) := by
  have ht : p3_2.t.Contains (quadraturePoint 3 2) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p3_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨2,by decide⟩
  have he : PointBox.calc p3_2.t = p3_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_3_contains : p3_3.Contains (quadraturePoint 3 3) := by
  have ht : p3_3.t.Contains (quadraturePoint 3 3) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p3_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨3,by decide⟩
  have he : PointBox.calc p3_3.t = p3_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_4_contains : p3_4.Contains (quadraturePoint 3 4) := by
  have ht : p3_4.t.Contains (quadraturePoint 3 4) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p3_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨4,by decide⟩
  have he : PointBox.calc p3_4.t = p3_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_5_contains : p3_5.Contains (quadraturePoint 3 5) := by
  have ht : p3_5.t.Contains (quadraturePoint 3 5) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p3_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨5,by decide⟩
  have he : PointBox.calc p3_5.t = p3_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_6_contains : p3_6.Contains (quadraturePoint 3 6) := by
  have ht : p3_6.t.Contains (quadraturePoint 3 6) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p3_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨6,by decide⟩
  have he : PointBox.calc p3_6.t = p3_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_7_contains : p3_7.Contains (quadraturePoint 3 7) := by
  have ht : p3_7.t.Contains (quadraturePoint 3 7) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p3_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨7,by decide⟩
  have he : PointBox.calc p3_7.t = p3_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_8_contains : p3_8.Contains (quadraturePoint 3 8) := by
  have ht : p3_8.t.Contains (quadraturePoint 3 8) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p3_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨8,by decide⟩
  have he : PointBox.calc p3_8.t = p3_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_9_contains : p3_9.Contains (quadraturePoint 3 9) := by
  have ht : p3_9.t.Contains (quadraturePoint 3 9) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p3_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨9,by decide⟩
  have he : PointBox.calc p3_9.t = p3_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_10_contains : p3_10.Contains (quadraturePoint 3 10) := by
  have ht : p3_10.t.Contains (quadraturePoint 3 10) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p3_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨10,by decide⟩
  have he : PointBox.calc p3_10.t = p3_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_11_contains : p3_11.Contains (quadraturePoint 3 11) := by
  have ht : p3_11.t.Contains (quadraturePoint 3 11) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p3_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨11,by decide⟩
  have he : PointBox.calc p3_11.t = p3_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_12_contains : p3_12.Contains (quadraturePoint 3 12) := by
  have ht : p3_12.t.Contains (quadraturePoint 3 12) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p3_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨12,by decide⟩
  have he : PointBox.calc p3_12.t = p3_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_13_contains : p3_13.Contains (quadraturePoint 3 13) := by
  have ht : p3_13.t.Contains (quadraturePoint 3 13) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p3_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨13,by decide⟩
  have he : PointBox.calc p3_13.t = p3_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_14_contains : p3_14.Contains (quadraturePoint 3 14) := by
  have ht : p3_14.t.Contains (quadraturePoint 3 14) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p3_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨14,by decide⟩
  have he : PointBox.calc p3_14.t = p3_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_15_contains : p3_15.Contains (quadraturePoint 3 15) := by
  have ht : p3_15.t.Contains (quadraturePoint 3 15) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p3_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨15,by decide⟩
  have he : PointBox.calc p3_15.t = p3_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_16_contains : p3_16.Contains (quadraturePoint 3 16) := by
  have ht : p3_16.t.Contains (quadraturePoint 3 16) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p3_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨16,by decide⟩
  have he : PointBox.calc p3_16.t = p3_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_17_contains : p3_17.Contains (quadraturePoint 3 17) := by
  have ht : p3_17.t.Contains (quadraturePoint 3 17) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p3_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨17,by decide⟩
  have he : PointBox.calc p3_17.t = p3_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_18_contains : p3_18.Contains (quadraturePoint 3 18) := by
  have ht : p3_18.t.Contains (quadraturePoint 3 18) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p3_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨18,by decide⟩
  have he : PointBox.calc p3_18.t = p3_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_19_contains : p3_19.Contains (quadraturePoint 3 19) := by
  have ht : p3_19.t.Contains (quadraturePoint 3 19) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p3_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨19,by decide⟩
  have he : PointBox.calc p3_19.t = p3_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_20_contains : p3_20.Contains (quadraturePoint 3 20) := by
  have ht : p3_20.t.Contains (quadraturePoint 3 20) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p3_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨20,by decide⟩
  have he : PointBox.calc p3_20.t = p3_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_21_contains : p3_21.Contains (quadraturePoint 3 21) := by
  have ht : p3_21.t.Contains (quadraturePoint 3 21) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p3_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨21,by decide⟩
  have he : PointBox.calc p3_21.t = p3_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_22_contains : p3_22.Contains (quadraturePoint 3 22) := by
  have ht : p3_22.t.Contains (quadraturePoint 3 22) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p3_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨22,by decide⟩
  have he : PointBox.calc p3_22.t = p3_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_23_contains : p3_23.Contains (quadraturePoint 3 23) := by
  have ht : p3_23.t.Contains (quadraturePoint 3 23) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p3_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨23,by decide⟩
  have he : PointBox.calc p3_23.t = p3_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_24_contains : p3_24.Contains (quadraturePoint 3 24) := by
  have ht : p3_24.t.Contains (quadraturePoint 3 24) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p3_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨24,by decide⟩
  have he : PointBox.calc p3_24.t = p3_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_25_contains : p3_25.Contains (quadraturePoint 3 25) := by
  have ht : p3_25.t.Contains (quadraturePoint 3 25) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p3_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨25,by decide⟩
  have he : PointBox.calc p3_25.t = p3_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_26_contains : p3_26.Contains (quadraturePoint 3 26) := by
  have ht : p3_26.t.Contains (quadraturePoint 3 26) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p3_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨26,by decide⟩
  have he : PointBox.calc p3_26.t = p3_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_27_contains : p3_27.Contains (quadraturePoint 3 27) := by
  have ht : p3_27.t.Contains (quadraturePoint 3 27) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p3_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨27,by decide⟩
  have he : PointBox.calc p3_27.t = p3_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_28_contains : p3_28.Contains (quadraturePoint 3 28) := by
  have ht : p3_28.t.Contains (quadraturePoint 3 28) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p3_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨28,by decide⟩
  have he : PointBox.calc p3_28.t = p3_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_29_contains : p3_29.Contains (quadraturePoint 3 29) := by
  have ht : p3_29.t.Contains (quadraturePoint 3 29) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p3_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨29,by decide⟩
  have he : PointBox.calc p3_29.t = p3_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_30_contains : p3_30.Contains (quadraturePoint 3 30) := by
  have ht : p3_30.t.Contains (quadraturePoint 3 30) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p3_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨30,by decide⟩
  have he : PointBox.calc p3_30.t = p3_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_31_contains : p3_31.Contains (quadraturePoint 3 31) := by
  have ht : p3_31.t.Contains (quadraturePoint 3 31) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p3_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨31,by decide⟩
  have he : PointBox.calc p3_31.t = p3_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_32_contains : p3_32.Contains (quadraturePoint 3 32) := by
  have ht : p3_32.t.Contains (quadraturePoint 3 32) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨32,by decide⟩).scale 1 12) = p3_32.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨32,by decide⟩
  have he : PointBox.calc p3_32.t = p3_32 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_33_contains : p3_33.Contains (quadraturePoint 3 33) := by
  have ht : p3_33.t.Contains (quadraturePoint 3 33) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨33,by decide⟩).scale 1 12) = p3_33.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨33,by decide⟩
  have he : PointBox.calc p3_33.t = p3_33 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_34_contains : p3_34.Contains (quadraturePoint 3 34) := by
  have ht : p3_34.t.Contains (quadraturePoint 3 34) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨34,by decide⟩).scale 1 12) = p3_34.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨34,by decide⟩
  have he : PointBox.calc p3_34.t = p3_34 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_35_contains : p3_35.Contains (quadraturePoint 3 35) := by
  have ht : p3_35.t.Contains (quadraturePoint 3 35) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨35,by decide⟩).scale 1 12) = p3_35.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨35,by decide⟩
  have he : PointBox.calc p3_35.t = p3_35 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_36_contains : p3_36.Contains (quadraturePoint 3 36) := by
  have ht : p3_36.t.Contains (quadraturePoint 3 36) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨36,by decide⟩).scale 1 12) = p3_36.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨36,by decide⟩
  have he : PointBox.calc p3_36.t = p3_36 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_37_contains : p3_37.Contains (quadraturePoint 3 37) := by
  have ht : p3_37.t.Contains (quadraturePoint 3 37) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨37,by decide⟩).scale 1 12) = p3_37.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨37,by decide⟩
  have he : PointBox.calc p3_37.t = p3_37 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_38_contains : p3_38.Contains (quadraturePoint 3 38) := by
  have ht : p3_38.t.Contains (quadraturePoint 3 38) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨38,by decide⟩).scale 1 12) = p3_38.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨38,by decide⟩
  have he : PointBox.calc p3_38.t = p3_38 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_39_contains : p3_39.Contains (quadraturePoint 3 39) := by
  have ht : p3_39.t.Contains (quadraturePoint 3 39) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨39,by decide⟩).scale 1 12) = p3_39.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨39,by decide⟩
  have he : PointBox.calc p3_39.t = p3_39 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_40_contains : p3_40.Contains (quadraturePoint 3 40) := by
  have ht : p3_40.t.Contains (quadraturePoint 3 40) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨40,by decide⟩).scale 1 12) = p3_40.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨40,by decide⟩
  have he : PointBox.calc p3_40.t = p3_40 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_41_contains : p3_41.Contains (quadraturePoint 3 41) := by
  have ht : p3_41.t.Contains (quadraturePoint 3 41) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨41,by decide⟩).scale 1 12) = p3_41.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨41,by decide⟩
  have he : PointBox.calc p3_41.t = p3_41 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_42_contains : p3_42.Contains (quadraturePoint 3 42) := by
  have ht : p3_42.t.Contains (quadraturePoint 3 42) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨42,by decide⟩).scale 1 12) = p3_42.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨42,by decide⟩
  have he : PointBox.calc p3_42.t = p3_42 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_43_contains : p3_43.Contains (quadraturePoint 3 43) := by
  have ht : p3_43.t.Contains (quadraturePoint 3 43) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨43,by decide⟩).scale 1 12) = p3_43.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨43,by decide⟩
  have he : PointBox.calc p3_43.t = p3_43 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_44_contains : p3_44.Contains (quadraturePoint 3 44) := by
  have ht : p3_44.t.Contains (quadraturePoint 3 44) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨44,by decide⟩).scale 1 12) = p3_44.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨44,by decide⟩
  have he : PointBox.calc p3_44.t = p3_44 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_45_contains : p3_45.Contains (quadraturePoint 3 45) := by
  have ht : p3_45.t.Contains (quadraturePoint 3 45) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨45,by decide⟩).scale 1 12) = p3_45.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨45,by decide⟩
  have he : PointBox.calc p3_45.t = p3_45 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_46_contains : p3_46.Contains (quadraturePoint 3 46) := by
  have ht : p3_46.t.Contains (quadraturePoint 3 46) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨46,by decide⟩).scale 1 12) = p3_46.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨46,by decide⟩
  have he : PointBox.calc p3_46.t = p3_46 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_47_contains : p3_47.Contains (quadraturePoint 3 47) := by
  have ht : p3_47.t.Contains (quadraturePoint 3 47) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨47,by decide⟩).scale 1 12) = p3_47.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨47,by decide⟩
  have he : PointBox.calc p3_47.t = p3_47 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_48_contains : p3_48.Contains (quadraturePoint 3 48) := by
  have ht : p3_48.t.Contains (quadraturePoint 3 48) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p3_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨48,by decide⟩
  have he : PointBox.calc p3_48.t = p3_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_49_contains : p3_49.Contains (quadraturePoint 3 49) := by
  have ht : p3_49.t.Contains (quadraturePoint 3 49) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p3_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨49,by decide⟩
  have he : PointBox.calc p3_49.t = p3_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_50_contains : p3_50.Contains (quadraturePoint 3 50) := by
  have ht : p3_50.t.Contains (quadraturePoint 3 50) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p3_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨50,by decide⟩
  have he : PointBox.calc p3_50.t = p3_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_51_contains : p3_51.Contains (quadraturePoint 3 51) := by
  have ht : p3_51.t.Contains (quadraturePoint 3 51) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p3_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨51,by decide⟩
  have he : PointBox.calc p3_51.t = p3_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_52_contains : p3_52.Contains (quadraturePoint 3 52) := by
  have ht : p3_52.t.Contains (quadraturePoint 3 52) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p3_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨52,by decide⟩
  have he : PointBox.calc p3_52.t = p3_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_53_contains : p3_53.Contains (quadraturePoint 3 53) := by
  have ht : p3_53.t.Contains (quadraturePoint 3 53) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p3_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨53,by decide⟩
  have he : PointBox.calc p3_53.t = p3_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_54_contains : p3_54.Contains (quadraturePoint 3 54) := by
  have ht : p3_54.t.Contains (quadraturePoint 3 54) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p3_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨54,by decide⟩
  have he : PointBox.calc p3_54.t = p3_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_55_contains : p3_55.Contains (quadraturePoint 3 55) := by
  have ht : p3_55.t.Contains (quadraturePoint 3 55) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p3_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨55,by decide⟩
  have he : PointBox.calc p3_55.t = p3_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_56_contains : p3_56.Contains (quadraturePoint 3 56) := by
  have ht : p3_56.t.Contains (quadraturePoint 3 56) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p3_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨56,by decide⟩
  have he : PointBox.calc p3_56.t = p3_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_57_contains : p3_57.Contains (quadraturePoint 3 57) := by
  have ht : p3_57.t.Contains (quadraturePoint 3 57) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p3_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨57,by decide⟩
  have he : PointBox.calc p3_57.t = p3_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_58_contains : p3_58.Contains (quadraturePoint 3 58) := by
  have ht : p3_58.t.Contains (quadraturePoint 3 58) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p3_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨58,by decide⟩
  have he : PointBox.calc p3_58.t = p3_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_59_contains : p3_59.Contains (quadraturePoint 3 59) := by
  have ht : p3_59.t.Contains (quadraturePoint 3 59) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p3_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨59,by decide⟩
  have he : PointBox.calc p3_59.t = p3_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_60_contains : p3_60.Contains (quadraturePoint 3 60) := by
  have ht : p3_60.t.Contains (quadraturePoint 3 60) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p3_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨60,by decide⟩
  have he : PointBox.calc p3_60.t = p3_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_61_contains : p3_61.Contains (quadraturePoint 3 61) := by
  have ht : p3_61.t.Contains (quadraturePoint 3 61) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p3_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨61,by decide⟩
  have he : PointBox.calc p3_61.t = p3_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_62_contains : p3_62.Contains (quadraturePoint 3 62) := by
  have ht : p3_62.t.Contains (quadraturePoint 3 62) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p3_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨62,by decide⟩
  have he : PointBox.calc p3_62.t = p3_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_63_contains : p3_63.Contains (quadraturePoint 3 63) := by
  have ht : p3_63.t.Contains (quadraturePoint 3 63) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p3_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨63,by decide⟩
  have he : PointBox.calc p3_63.t = p3_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_64_contains : p3_64.Contains (quadraturePoint 3 64) := by
  have ht : p3_64.t.Contains (quadraturePoint 3 64) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p3_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨64,by decide⟩
  have he : PointBox.calc p3_64.t = p3_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_65_contains : p3_65.Contains (quadraturePoint 3 65) := by
  have ht : p3_65.t.Contains (quadraturePoint 3 65) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p3_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨65,by decide⟩
  have he : PointBox.calc p3_65.t = p3_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_66_contains : p3_66.Contains (quadraturePoint 3 66) := by
  have ht : p3_66.t.Contains (quadraturePoint 3 66) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p3_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨66,by decide⟩
  have he : PointBox.calc p3_66.t = p3_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_67_contains : p3_67.Contains (quadraturePoint 3 67) := by
  have ht : p3_67.t.Contains (quadraturePoint 3 67) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p3_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨67,by decide⟩
  have he : PointBox.calc p3_67.t = p3_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_68_contains : p3_68.Contains (quadraturePoint 3 68) := by
  have ht : p3_68.t.Contains (quadraturePoint 3 68) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p3_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨68,by decide⟩
  have he : PointBox.calc p3_68.t = p3_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_69_contains : p3_69.Contains (quadraturePoint 3 69) := by
  have ht : p3_69.t.Contains (quadraturePoint 3 69) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p3_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨69,by decide⟩
  have he : PointBox.calc p3_69.t = p3_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_70_contains : p3_70.Contains (quadraturePoint 3 70) := by
  have ht : p3_70.t.Contains (quadraturePoint 3 70) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p3_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨70,by decide⟩
  have he : PointBox.calc p3_70.t = p3_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_71_contains : p3_71.Contains (quadraturePoint 3 71) := by
  have ht : p3_71.t.Contains (quadraturePoint 3 71) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p3_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨71,by decide⟩
  have he : PointBox.calc p3_71.t = p3_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_72_contains : p3_72.Contains (quadraturePoint 3 72) := by
  have ht : p3_72.t.Contains (quadraturePoint 3 72) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p3_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨72,by decide⟩
  have he : PointBox.calc p3_72.t = p3_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_73_contains : p3_73.Contains (quadraturePoint 3 73) := by
  have ht : p3_73.t.Contains (quadraturePoint 3 73) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p3_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨73,by decide⟩
  have he : PointBox.calc p3_73.t = p3_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_74_contains : p3_74.Contains (quadraturePoint 3 74) := by
  have ht : p3_74.t.Contains (quadraturePoint 3 74) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p3_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨74,by decide⟩
  have he : PointBox.calc p3_74.t = p3_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_75_contains : p3_75.Contains (quadraturePoint 3 75) := by
  have ht : p3_75.t.Contains (quadraturePoint 3 75) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p3_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨75,by decide⟩
  have he : PointBox.calc p3_75.t = p3_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_76_contains : p3_76.Contains (quadraturePoint 3 76) := by
  have ht : p3_76.t.Contains (quadraturePoint 3 76) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p3_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨76,by decide⟩
  have he : PointBox.calc p3_76.t = p3_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_77_contains : p3_77.Contains (quadraturePoint 3 77) := by
  have ht : p3_77.t.Contains (quadraturePoint 3 77) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p3_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨77,by decide⟩
  have he : PointBox.calc p3_77.t = p3_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_78_contains : p3_78.Contains (quadraturePoint 3 78) := by
  have ht : p3_78.t.Contains (quadraturePoint 3 78) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p3_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨78,by decide⟩
  have he : PointBox.calc p3_78.t = p3_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_79_contains : p3_79.Contains (quadraturePoint 3 79) := by
  have ht : p3_79.t.Contains (quadraturePoint 3 79) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p3_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨79,by decide⟩
  have he : PointBox.calc p3_79.t = p3_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_80_contains : p3_80.Contains (quadraturePoint 3 80) := by
  have ht : p3_80.t.Contains (quadraturePoint 3 80) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p3_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨80,by decide⟩
  have he : PointBox.calc p3_80.t = p3_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_81_contains : p3_81.Contains (quadraturePoint 3 81) := by
  have ht : p3_81.t.Contains (quadraturePoint 3 81) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p3_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨81,by decide⟩
  have he : PointBox.calc p3_81.t = p3_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_82_contains : p3_82.Contains (quadraturePoint 3 82) := by
  have ht : p3_82.t.Contains (quadraturePoint 3 82) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p3_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨82,by decide⟩
  have he : PointBox.calc p3_82.t = p3_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_83_contains : p3_83.Contains (quadraturePoint 3 83) := by
  have ht : p3_83.t.Contains (quadraturePoint 3 83) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p3_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨83,by decide⟩
  have he : PointBox.calc p3_83.t = p3_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_84_contains : p3_84.Contains (quadraturePoint 3 84) := by
  have ht : p3_84.t.Contains (quadraturePoint 3 84) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p3_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨84,by decide⟩
  have he : PointBox.calc p3_84.t = p3_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_85_contains : p3_85.Contains (quadraturePoint 3 85) := by
  have ht : p3_85.t.Contains (quadraturePoint 3 85) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p3_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨85,by decide⟩
  have he : PointBox.calc p3_85.t = p3_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_86_contains : p3_86.Contains (quadraturePoint 3 86) := by
  have ht : p3_86.t.Contains (quadraturePoint 3 86) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p3_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨86,by decide⟩
  have he : PointBox.calc p3_86.t = p3_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_87_contains : p3_87.Contains (quadraturePoint 3 87) := by
  have ht : p3_87.t.Contains (quadraturePoint 3 87) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p3_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨87,by decide⟩
  have he : PointBox.calc p3_87.t = p3_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_88_contains : p3_88.Contains (quadraturePoint 3 88) := by
  have ht : p3_88.t.Contains (quadraturePoint 3 88) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p3_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨88,by decide⟩
  have he : PointBox.calc p3_88.t = p3_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_89_contains : p3_89.Contains (quadraturePoint 3 89) := by
  have ht : p3_89.t.Contains (quadraturePoint 3 89) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p3_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨89,by decide⟩
  have he : PointBox.calc p3_89.t = p3_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_90_contains : p3_90.Contains (quadraturePoint 3 90) := by
  have ht : p3_90.t.Contains (quadraturePoint 3 90) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p3_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨90,by decide⟩
  have he : PointBox.calc p3_90.t = p3_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_91_contains : p3_91.Contains (quadraturePoint 3 91) := by
  have ht : p3_91.t.Contains (quadraturePoint 3 91) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p3_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨91,by decide⟩
  have he : PointBox.calc p3_91.t = p3_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_92_contains : p3_92.Contains (quadraturePoint 3 92) := by
  have ht : p3_92.t.Contains (quadraturePoint 3 92) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p3_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨92,by decide⟩
  have he : PointBox.calc p3_92.t = p3_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_93_contains : p3_93.Contains (quadraturePoint 3 93) := by
  have ht : p3_93.t.Contains (quadraturePoint 3 93) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p3_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨93,by decide⟩
  have he : PointBox.calc p3_93.t = p3_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_94_contains : p3_94.Contains (quadraturePoint 3 94) := by
  have ht : p3_94.t.Contains (quadraturePoint 3 94) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p3_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨94,by decide⟩
  have he : PointBox.calc p3_94.t = p3_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_95_contains : p3_95.Contains (quadraturePoint 3 95) := by
  have ht : p3_95.t.Contains (quadraturePoint 3 95) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p3_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨95,by decide⟩
  have he : PointBox.calc p3_95.t = p3_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_96_contains : p3_96.Contains (quadraturePoint 3 96) := by
  have ht : p3_96.t.Contains (quadraturePoint 3 96) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨96,by decide⟩).scale 1 12) = p3_96.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨96,by decide⟩
  have he : PointBox.calc p3_96.t = p3_96 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_97_contains : p3_97.Contains (quadraturePoint 3 97) := by
  have ht : p3_97.t.Contains (quadraturePoint 3 97) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p3_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨97,by decide⟩
  have he : PointBox.calc p3_97.t = p3_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_98_contains : p3_98.Contains (quadraturePoint 3 98) := by
  have ht : p3_98.t.Contains (quadraturePoint 3 98) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨98,by decide⟩).scale 1 12) = p3_98.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨98,by decide⟩
  have he : PointBox.calc p3_98.t = p3_98 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_99_contains : p3_99.Contains (quadraturePoint 3 99) := by
  have ht : p3_99.t.Contains (quadraturePoint 3 99) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨99,by decide⟩).scale 1 12) = p3_99.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨99,by decide⟩
  have he : PointBox.calc p3_99.t = p3_99 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_100_contains : p3_100.Contains (quadraturePoint 3 100) := by
  have ht : p3_100.t.Contains (quadraturePoint 3 100) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨100,by decide⟩).scale 1 12) = p3_100.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨100,by decide⟩
  have he : PointBox.calc p3_100.t = p3_100 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_101_contains : p3_101.Contains (quadraturePoint 3 101) := by
  have ht : p3_101.t.Contains (quadraturePoint 3 101) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨101,by decide⟩).scale 1 12) = p3_101.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨101,by decide⟩
  have he : PointBox.calc p3_101.t = p3_101 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_102_contains : p3_102.Contains (quadraturePoint 3 102) := by
  have ht : p3_102.t.Contains (quadraturePoint 3 102) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨102,by decide⟩).scale 1 12) = p3_102.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨102,by decide⟩
  have he : PointBox.calc p3_102.t = p3_102 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_103_contains : p3_103.Contains (quadraturePoint 3 103) := by
  have ht : p3_103.t.Contains (quadraturePoint 3 103) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨103,by decide⟩).scale 1 12) = p3_103.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨103,by decide⟩
  have he : PointBox.calc p3_103.t = p3_103 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_104_contains : p3_104.Contains (quadraturePoint 3 104) := by
  have ht : p3_104.t.Contains (quadraturePoint 3 104) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨104,by decide⟩).scale 1 12) = p3_104.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨104,by decide⟩
  have he : PointBox.calc p3_104.t = p3_104 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_105_contains : p3_105.Contains (quadraturePoint 3 105) := by
  have ht : p3_105.t.Contains (quadraturePoint 3 105) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨105,by decide⟩).scale 1 12) = p3_105.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨105,by decide⟩
  have he : PointBox.calc p3_105.t = p3_105 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_106_contains : p3_106.Contains (quadraturePoint 3 106) := by
  have ht : p3_106.t.Contains (quadraturePoint 3 106) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨106,by decide⟩).scale 1 12) = p3_106.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨106,by decide⟩
  have he : PointBox.calc p3_106.t = p3_106 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_107_contains : p3_107.Contains (quadraturePoint 3 107) := by
  have ht : p3_107.t.Contains (quadraturePoint 3 107) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨107,by decide⟩).scale 1 12) = p3_107.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨107,by decide⟩
  have he : PointBox.calc p3_107.t = p3_107 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_108_contains : p3_108.Contains (quadraturePoint 3 108) := by
  have ht : p3_108.t.Contains (quadraturePoint 3 108) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨108,by decide⟩).scale 1 12) = p3_108.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨108,by decide⟩
  have he : PointBox.calc p3_108.t = p3_108 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_109_contains : p3_109.Contains (quadraturePoint 3 109) := by
  have ht : p3_109.t.Contains (quadraturePoint 3 109) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨109,by decide⟩).scale 1 12) = p3_109.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨109,by decide⟩
  have he : PointBox.calc p3_109.t = p3_109 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_110_contains : p3_110.Contains (quadraturePoint 3 110) := by
  have ht : p3_110.t.Contains (quadraturePoint 3 110) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨110,by decide⟩).scale 1 12) = p3_110.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨110,by decide⟩
  have he : PointBox.calc p3_110.t = p3_110 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_111_contains : p3_111.Contains (quadraturePoint 3 111) := by
  have ht : p3_111.t.Contains (quadraturePoint 3 111) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨111,by decide⟩).scale 1 12) = p3_111.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨111,by decide⟩
  have he : PointBox.calc p3_111.t = p3_111 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_224_contains : p3_224.Contains (quadraturePoint 3 224) := by
  have ht : p3_224.t.Contains (quadraturePoint 3 224) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p3_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨224,by decide⟩
  have he : PointBox.calc p3_224.t = p3_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_225_contains : p3_225.Contains (quadraturePoint 3 225) := by
  have ht : p3_225.t.Contains (quadraturePoint 3 225) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p3_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨225,by decide⟩
  have he : PointBox.calc p3_225.t = p3_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_226_contains : p3_226.Contains (quadraturePoint 3 226) := by
  have ht : p3_226.t.Contains (quadraturePoint 3 226) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p3_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨226,by decide⟩
  have he : PointBox.calc p3_226.t = p3_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_227_contains : p3_227.Contains (quadraturePoint 3 227) := by
  have ht : p3_227.t.Contains (quadraturePoint 3 227) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p3_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨227,by decide⟩
  have he : PointBox.calc p3_227.t = p3_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_228_contains : p3_228.Contains (quadraturePoint 3 228) := by
  have ht : p3_228.t.Contains (quadraturePoint 3 228) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p3_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨228,by decide⟩
  have he : PointBox.calc p3_228.t = p3_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_229_contains : p3_229.Contains (quadraturePoint 3 229) := by
  have ht : p3_229.t.Contains (quadraturePoint 3 229) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p3_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨229,by decide⟩
  have he : PointBox.calc p3_229.t = p3_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_230_contains : p3_230.Contains (quadraturePoint 3 230) := by
  have ht : p3_230.t.Contains (quadraturePoint 3 230) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p3_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨230,by decide⟩
  have he : PointBox.calc p3_230.t = p3_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_231_contains : p3_231.Contains (quadraturePoint 3 231) := by
  have ht : p3_231.t.Contains (quadraturePoint 3 231) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p3_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨231,by decide⟩
  have he : PointBox.calc p3_231.t = p3_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_232_contains : p3_232.Contains (quadraturePoint 3 232) := by
  have ht : p3_232.t.Contains (quadraturePoint 3 232) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p3_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨232,by decide⟩
  have he : PointBox.calc p3_232.t = p3_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_233_contains : p3_233.Contains (quadraturePoint 3 233) := by
  have ht : p3_233.t.Contains (quadraturePoint 3 233) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p3_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨233,by decide⟩
  have he : PointBox.calc p3_233.t = p3_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_234_contains : p3_234.Contains (quadraturePoint 3 234) := by
  have ht : p3_234.t.Contains (quadraturePoint 3 234) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p3_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨234,by decide⟩
  have he : PointBox.calc p3_234.t = p3_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_235_contains : p3_235.Contains (quadraturePoint 3 235) := by
  have ht : p3_235.t.Contains (quadraturePoint 3 235) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p3_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨235,by decide⟩
  have he : PointBox.calc p3_235.t = p3_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_236_contains : p3_236.Contains (quadraturePoint 3 236) := by
  have ht : p3_236.t.Contains (quadraturePoint 3 236) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p3_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨236,by decide⟩
  have he : PointBox.calc p3_236.t = p3_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_237_contains : p3_237.Contains (quadraturePoint 3 237) := by
  have ht : p3_237.t.Contains (quadraturePoint 3 237) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p3_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨237,by decide⟩
  have he : PointBox.calc p3_237.t = p3_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_238_contains : p3_238.Contains (quadraturePoint 3 238) := by
  have ht : p3_238.t.Contains (quadraturePoint 3 238) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p3_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨238,by decide⟩
  have he : PointBox.calc p3_238.t = p3_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_239_contains : p3_239.Contains (quadraturePoint 3 239) := by
  have ht : p3_239.t.Contains (quadraturePoint 3 239) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p3_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨239,by decide⟩
  have he : PointBox.calc p3_239.t = p3_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_240_contains : p3_240.Contains (quadraturePoint 3 240) := by
  have ht : p3_240.t.Contains (quadraturePoint 3 240) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨240,by decide⟩).scale 1 12) = p3_240.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨240,by decide⟩
  have he : PointBox.calc p3_240.t = p3_240 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_241_contains : p3_241.Contains (quadraturePoint 3 241) := by
  have ht : p3_241.t.Contains (quadraturePoint 3 241) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨241,by decide⟩).scale 1 12) = p3_241.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨241,by decide⟩
  have he : PointBox.calc p3_241.t = p3_241 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_242_contains : p3_242.Contains (quadraturePoint 3 242) := by
  have ht : p3_242.t.Contains (quadraturePoint 3 242) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨242,by decide⟩).scale 1 12) = p3_242.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨242,by decide⟩
  have he : PointBox.calc p3_242.t = p3_242 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_243_contains : p3_243.Contains (quadraturePoint 3 243) := by
  have ht : p3_243.t.Contains (quadraturePoint 3 243) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨243,by decide⟩).scale 1 12) = p3_243.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨243,by decide⟩
  have he : PointBox.calc p3_243.t = p3_243 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_244_contains : p3_244.Contains (quadraturePoint 3 244) := by
  have ht : p3_244.t.Contains (quadraturePoint 3 244) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨244,by decide⟩).scale 1 12) = p3_244.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨244,by decide⟩
  have he : PointBox.calc p3_244.t = p3_244 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_245_contains : p3_245.Contains (quadraturePoint 3 245) := by
  have ht : p3_245.t.Contains (quadraturePoint 3 245) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨245,by decide⟩).scale 1 12) = p3_245.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨245,by decide⟩
  have he : PointBox.calc p3_245.t = p3_245 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_246_contains : p3_246.Contains (quadraturePoint 3 246) := by
  have ht : p3_246.t.Contains (quadraturePoint 3 246) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨246,by decide⟩).scale 1 12) = p3_246.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨246,by decide⟩
  have he : PointBox.calc p3_246.t = p3_246 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_247_contains : p3_247.Contains (quadraturePoint 3 247) := by
  have ht : p3_247.t.Contains (quadraturePoint 3 247) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨247,by decide⟩).scale 1 12) = p3_247.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨247,by decide⟩
  have he : PointBox.calc p3_247.t = p3_247 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_248_contains : p3_248.Contains (quadraturePoint 3 248) := by
  have ht : p3_248.t.Contains (quadraturePoint 3 248) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨248,by decide⟩).scale 1 12) = p3_248.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨248,by decide⟩
  have he : PointBox.calc p3_248.t = p3_248 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_249_contains : p3_249.Contains (quadraturePoint 3 249) := by
  have ht : p3_249.t.Contains (quadraturePoint 3 249) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨249,by decide⟩).scale 1 12) = p3_249.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨249,by decide⟩
  have he : PointBox.calc p3_249.t = p3_249 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_250_contains : p3_250.Contains (quadraturePoint 3 250) := by
  have ht : p3_250.t.Contains (quadraturePoint 3 250) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨250,by decide⟩).scale 1 12) = p3_250.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨250,by decide⟩
  have he : PointBox.calc p3_250.t = p3_250 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_251_contains : p3_251.Contains (quadraturePoint 3 251) := by
  have ht : p3_251.t.Contains (quadraturePoint 3 251) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨251,by decide⟩).scale 1 12) = p3_251.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨251,by decide⟩
  have he : PointBox.calc p3_251.t = p3_251 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_252_contains : p3_252.Contains (quadraturePoint 3 252) := by
  have ht : p3_252.t.Contains (quadraturePoint 3 252) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨252,by decide⟩).scale 1 12) = p3_252.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨252,by decide⟩
  have he : PointBox.calc p3_252.t = p3_252 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_253_contains : p3_253.Contains (quadraturePoint 3 253) := by
  have ht : p3_253.t.Contains (quadraturePoint 3 253) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨253,by decide⟩).scale 1 12) = p3_253.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨253,by decide⟩
  have he : PointBox.calc p3_253.t = p3_253 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_254_contains : p3_254.Contains (quadraturePoint 3 254) := by
  have ht : p3_254.t.Contains (quadraturePoint 3 254) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨254,by decide⟩).scale 1 12) = p3_254.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨254,by decide⟩
  have he : PointBox.calc p3_254.t = p3_254 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_255_contains : p3_255.Contains (quadraturePoint 3 255) := by
  have ht : p3_255.t.Contains (quadraturePoint 3 255) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨255,by decide⟩).scale 1 12) = p3_255.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨255,by decide⟩
  have he : PointBox.calc p3_255.t = p3_255 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row3_0_contains (k : Fin 16) : (row3_0 k).Contains (quadraturePoint 3 (0+k.val)) := by
  fin_cases k
  · exact p3_0_contains
  · exact p3_1_contains
  · exact p3_2_contains
  · exact p3_3_contains
  · exact p3_4_contains
  · exact p3_5_contains
  · exact p3_6_contains
  · exact p3_7_contains
  · exact p3_8_contains
  · exact p3_9_contains
  · exact p3_10_contains
  · exact p3_11_contains
  · exact p3_12_contains
  · exact p3_13_contains
  · exact p3_14_contains
  · exact p3_15_contains
lemma row3_1_contains (k : Fin 16) : (row3_1 k).Contains (quadraturePoint 3 (16+k.val)) := by
  fin_cases k
  · exact p3_16_contains
  · exact p3_17_contains
  · exact p3_18_contains
  · exact p3_19_contains
  · exact p3_20_contains
  · exact p3_21_contains
  · exact p3_22_contains
  · exact p3_23_contains
  · exact p3_24_contains
  · exact p3_25_contains
  · exact p3_26_contains
  · exact p3_27_contains
  · exact p3_28_contains
  · exact p3_29_contains
  · exact p3_30_contains
  · exact p3_31_contains
lemma row3_2_contains (k : Fin 16) : (row3_2 k).Contains (quadraturePoint 3 (32+k.val)) := by
  fin_cases k
  · exact p3_32_contains
  · exact p3_33_contains
  · exact p3_34_contains
  · exact p3_35_contains
  · exact p3_36_contains
  · exact p3_37_contains
  · exact p3_38_contains
  · exact p3_39_contains
  · exact p3_40_contains
  · exact p3_41_contains
  · exact p3_42_contains
  · exact p3_43_contains
  · exact p3_44_contains
  · exact p3_45_contains
  · exact p3_46_contains
  · exact p3_47_contains
lemma row3_3_contains (k : Fin 16) : (row3_3 k).Contains (quadraturePoint 3 (48+k.val)) := by
  fin_cases k
  · exact p3_48_contains
  · exact p3_49_contains
  · exact p3_50_contains
  · exact p3_51_contains
  · exact p3_52_contains
  · exact p3_53_contains
  · exact p3_54_contains
  · exact p3_55_contains
  · exact p3_56_contains
  · exact p3_57_contains
  · exact p3_58_contains
  · exact p3_59_contains
  · exact p3_60_contains
  · exact p3_61_contains
  · exact p3_62_contains
  · exact p3_63_contains
lemma row3_4_contains (k : Fin 16) : (row3_4 k).Contains (quadraturePoint 3 (64+k.val)) := by
  fin_cases k
  · exact p3_64_contains
  · exact p3_65_contains
  · exact p3_66_contains
  · exact p3_67_contains
  · exact p3_68_contains
  · exact p3_69_contains
  · exact p3_70_contains
  · exact p3_71_contains
  · exact p3_72_contains
  · exact p3_73_contains
  · exact p3_74_contains
  · exact p3_75_contains
  · exact p3_76_contains
  · exact p3_77_contains
  · exact p3_78_contains
  · exact p3_79_contains
lemma row3_5_contains (k : Fin 16) : (row3_5 k).Contains (quadraturePoint 3 (80+k.val)) := by
  fin_cases k
  · exact p3_80_contains
  · exact p3_81_contains
  · exact p3_82_contains
  · exact p3_83_contains
  · exact p3_84_contains
  · exact p3_85_contains
  · exact p3_86_contains
  · exact p3_87_contains
  · exact p3_88_contains
  · exact p3_89_contains
  · exact p3_90_contains
  · exact p3_91_contains
  · exact p3_92_contains
  · exact p3_93_contains
  · exact p3_94_contains
  · exact p3_95_contains
lemma row3_6_contains (k : Fin 16) : (row3_6 k).Contains (quadraturePoint 3 (96+k.val)) := by
  fin_cases k
  · exact p3_96_contains
  · exact p3_97_contains
  · exact p3_98_contains
  · exact p3_99_contains
  · exact p3_100_contains
  · exact p3_101_contains
  · exact p3_102_contains
  · exact p3_103_contains
  · exact p3_104_contains
  · exact p3_105_contains
  · exact p3_106_contains
  · exact p3_107_contains
  · exact p3_108_contains
  · exact p3_109_contains
  · exact p3_110_contains
  · exact p3_111_contains
lemma row3_14_contains (k : Fin 16) : (row3_14 k).Contains (quadraturePoint 3 (224+k.val)) := by
  fin_cases k
  · exact p3_224_contains
  · exact p3_225_contains
  · exact p3_226_contains
  · exact p3_227_contains
  · exact p3_228_contains
  · exact p3_229_contains
  · exact p3_230_contains
  · exact p3_231_contains
  · exact p3_232_contains
  · exact p3_233_contains
  · exact p3_234_contains
  · exact p3_235_contains
  · exact p3_236_contains
  · exact p3_237_contains
  · exact p3_238_contains
  · exact p3_239_contains
lemma row3_15_contains (k : Fin 16) : (row3_15 k).Contains (quadraturePoint 3 (240+k.val)) := by
  fin_cases k
  · exact p3_240_contains
  · exact p3_241_contains
  · exact p3_242_contains
  · exact p3_243_contains
  · exact p3_244_contains
  · exact p3_245_contains
  · exact p3_246_contains
  · exact p3_247_contains
  · exact p3_248_contains
  · exact p3_249_contains
  · exact p3_250_contains
  · exact p3_251_contains
  · exact p3_252_contains
  · exact p3_253_contains
  · exact p3_254_contains
  · exact p3_255_contains
lemma row3_contains_g_oai (i k : Fin 16) : (row3 i k).Contains (quadraturePoint 3 (16*i.val+k.val)) := by
  fin_cases i
  · exact row3_0_contains k
  · exact row3_1_contains k
  · exact row3_2_contains k
  · exact row3_3_contains k
  · exact row3_4_contains k
  · exact row3_5_contains k
  · exact row3_6_contains k
  · exact row3_7_contains_g k
  · exact row3_8_contains_g k
  · exact row3_9_contains_g k
  · exact row3_10_contains_g k
  · exact row3_11_contains_g k
  · exact row3_12_contains_g k
  · exact row3_13_contains_g k
  · exact row3_14_contains k
  · exact row3_15_contains k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row3_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row3_contains_g_oai
