-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:12.845215+00:00
-- url     : https://prove2.me/submissions/385cea96-a194-4afb-963e-491eab967966

import Mathlib
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_8_contains_g
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

lemma p2_0_contains : p2_0.Contains (quadraturePoint 2 0) := by
  have ht : p2_0.t.Contains (quadraturePoint 2 0) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p2_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨0,by decide⟩
  have he : PointBox.calc p2_0.t = p2_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_1_contains : p2_1.Contains (quadraturePoint 2 1) := by
  have ht : p2_1.t.Contains (quadraturePoint 2 1) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p2_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨1,by decide⟩
  have he : PointBox.calc p2_1.t = p2_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_2_contains : p2_2.Contains (quadraturePoint 2 2) := by
  have ht : p2_2.t.Contains (quadraturePoint 2 2) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p2_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨2,by decide⟩
  have he : PointBox.calc p2_2.t = p2_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_3_contains : p2_3.Contains (quadraturePoint 2 3) := by
  have ht : p2_3.t.Contains (quadraturePoint 2 3) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p2_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨3,by decide⟩
  have he : PointBox.calc p2_3.t = p2_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_4_contains : p2_4.Contains (quadraturePoint 2 4) := by
  have ht : p2_4.t.Contains (quadraturePoint 2 4) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p2_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨4,by decide⟩
  have he : PointBox.calc p2_4.t = p2_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_5_contains : p2_5.Contains (quadraturePoint 2 5) := by
  have ht : p2_5.t.Contains (quadraturePoint 2 5) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p2_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨5,by decide⟩
  have he : PointBox.calc p2_5.t = p2_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_6_contains : p2_6.Contains (quadraturePoint 2 6) := by
  have ht : p2_6.t.Contains (quadraturePoint 2 6) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p2_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨6,by decide⟩
  have he : PointBox.calc p2_6.t = p2_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_7_contains : p2_7.Contains (quadraturePoint 2 7) := by
  have ht : p2_7.t.Contains (quadraturePoint 2 7) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p2_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨7,by decide⟩
  have he : PointBox.calc p2_7.t = p2_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_8_contains : p2_8.Contains (quadraturePoint 2 8) := by
  have ht : p2_8.t.Contains (quadraturePoint 2 8) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p2_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨8,by decide⟩
  have he : PointBox.calc p2_8.t = p2_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_9_contains : p2_9.Contains (quadraturePoint 2 9) := by
  have ht : p2_9.t.Contains (quadraturePoint 2 9) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p2_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨9,by decide⟩
  have he : PointBox.calc p2_9.t = p2_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_10_contains : p2_10.Contains (quadraturePoint 2 10) := by
  have ht : p2_10.t.Contains (quadraturePoint 2 10) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p2_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨10,by decide⟩
  have he : PointBox.calc p2_10.t = p2_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_11_contains : p2_11.Contains (quadraturePoint 2 11) := by
  have ht : p2_11.t.Contains (quadraturePoint 2 11) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p2_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨11,by decide⟩
  have he : PointBox.calc p2_11.t = p2_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_12_contains : p2_12.Contains (quadraturePoint 2 12) := by
  have ht : p2_12.t.Contains (quadraturePoint 2 12) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p2_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨12,by decide⟩
  have he : PointBox.calc p2_12.t = p2_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_13_contains : p2_13.Contains (quadraturePoint 2 13) := by
  have ht : p2_13.t.Contains (quadraturePoint 2 13) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p2_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨13,by decide⟩
  have he : PointBox.calc p2_13.t = p2_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_14_contains : p2_14.Contains (quadraturePoint 2 14) := by
  have ht : p2_14.t.Contains (quadraturePoint 2 14) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p2_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨14,by decide⟩
  have he : PointBox.calc p2_14.t = p2_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_15_contains : p2_15.Contains (quadraturePoint 2 15) := by
  have ht : p2_15.t.Contains (quadraturePoint 2 15) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p2_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨15,by decide⟩
  have he : PointBox.calc p2_15.t = p2_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_16_contains : p2_16.Contains (quadraturePoint 2 16) := by
  have ht : p2_16.t.Contains (quadraturePoint 2 16) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p2_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨16,by decide⟩
  have he : PointBox.calc p2_16.t = p2_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_17_contains : p2_17.Contains (quadraturePoint 2 17) := by
  have ht : p2_17.t.Contains (quadraturePoint 2 17) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p2_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨17,by decide⟩
  have he : PointBox.calc p2_17.t = p2_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_18_contains : p2_18.Contains (quadraturePoint 2 18) := by
  have ht : p2_18.t.Contains (quadraturePoint 2 18) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p2_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨18,by decide⟩
  have he : PointBox.calc p2_18.t = p2_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_19_contains : p2_19.Contains (quadraturePoint 2 19) := by
  have ht : p2_19.t.Contains (quadraturePoint 2 19) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p2_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨19,by decide⟩
  have he : PointBox.calc p2_19.t = p2_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_20_contains : p2_20.Contains (quadraturePoint 2 20) := by
  have ht : p2_20.t.Contains (quadraturePoint 2 20) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p2_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨20,by decide⟩
  have he : PointBox.calc p2_20.t = p2_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_21_contains : p2_21.Contains (quadraturePoint 2 21) := by
  have ht : p2_21.t.Contains (quadraturePoint 2 21) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p2_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨21,by decide⟩
  have he : PointBox.calc p2_21.t = p2_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_22_contains : p2_22.Contains (quadraturePoint 2 22) := by
  have ht : p2_22.t.Contains (quadraturePoint 2 22) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p2_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨22,by decide⟩
  have he : PointBox.calc p2_22.t = p2_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_23_contains : p2_23.Contains (quadraturePoint 2 23) := by
  have ht : p2_23.t.Contains (quadraturePoint 2 23) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p2_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨23,by decide⟩
  have he : PointBox.calc p2_23.t = p2_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_24_contains : p2_24.Contains (quadraturePoint 2 24) := by
  have ht : p2_24.t.Contains (quadraturePoint 2 24) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p2_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨24,by decide⟩
  have he : PointBox.calc p2_24.t = p2_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_25_contains : p2_25.Contains (quadraturePoint 2 25) := by
  have ht : p2_25.t.Contains (quadraturePoint 2 25) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p2_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨25,by decide⟩
  have he : PointBox.calc p2_25.t = p2_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_26_contains : p2_26.Contains (quadraturePoint 2 26) := by
  have ht : p2_26.t.Contains (quadraturePoint 2 26) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p2_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨26,by decide⟩
  have he : PointBox.calc p2_26.t = p2_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_27_contains : p2_27.Contains (quadraturePoint 2 27) := by
  have ht : p2_27.t.Contains (quadraturePoint 2 27) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p2_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨27,by decide⟩
  have he : PointBox.calc p2_27.t = p2_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_28_contains : p2_28.Contains (quadraturePoint 2 28) := by
  have ht : p2_28.t.Contains (quadraturePoint 2 28) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p2_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨28,by decide⟩
  have he : PointBox.calc p2_28.t = p2_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_29_contains : p2_29.Contains (quadraturePoint 2 29) := by
  have ht : p2_29.t.Contains (quadraturePoint 2 29) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p2_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨29,by decide⟩
  have he : PointBox.calc p2_29.t = p2_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_30_contains : p2_30.Contains (quadraturePoint 2 30) := by
  have ht : p2_30.t.Contains (quadraturePoint 2 30) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p2_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨30,by decide⟩
  have he : PointBox.calc p2_30.t = p2_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_31_contains : p2_31.Contains (quadraturePoint 2 31) := by
  have ht : p2_31.t.Contains (quadraturePoint 2 31) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p2_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨31,by decide⟩
  have he : PointBox.calc p2_31.t = p2_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_32_contains : p2_32.Contains (quadraturePoint 2 32) := by
  have ht : p2_32.t.Contains (quadraturePoint 2 32) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨32,by decide⟩).scale 1 12) = p2_32.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨32,by decide⟩
  have he : PointBox.calc p2_32.t = p2_32 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_33_contains : p2_33.Contains (quadraturePoint 2 33) := by
  have ht : p2_33.t.Contains (quadraturePoint 2 33) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨33,by decide⟩).scale 1 12) = p2_33.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨33,by decide⟩
  have he : PointBox.calc p2_33.t = p2_33 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_34_contains : p2_34.Contains (quadraturePoint 2 34) := by
  have ht : p2_34.t.Contains (quadraturePoint 2 34) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨34,by decide⟩).scale 1 12) = p2_34.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨34,by decide⟩
  have he : PointBox.calc p2_34.t = p2_34 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_35_contains : p2_35.Contains (quadraturePoint 2 35) := by
  have ht : p2_35.t.Contains (quadraturePoint 2 35) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨35,by decide⟩).scale 1 12) = p2_35.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨35,by decide⟩
  have he : PointBox.calc p2_35.t = p2_35 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_36_contains : p2_36.Contains (quadraturePoint 2 36) := by
  have ht : p2_36.t.Contains (quadraturePoint 2 36) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨36,by decide⟩).scale 1 12) = p2_36.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨36,by decide⟩
  have he : PointBox.calc p2_36.t = p2_36 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_37_contains : p2_37.Contains (quadraturePoint 2 37) := by
  have ht : p2_37.t.Contains (quadraturePoint 2 37) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨37,by decide⟩).scale 1 12) = p2_37.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨37,by decide⟩
  have he : PointBox.calc p2_37.t = p2_37 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_38_contains : p2_38.Contains (quadraturePoint 2 38) := by
  have ht : p2_38.t.Contains (quadraturePoint 2 38) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨38,by decide⟩).scale 1 12) = p2_38.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨38,by decide⟩
  have he : PointBox.calc p2_38.t = p2_38 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_39_contains : p2_39.Contains (quadraturePoint 2 39) := by
  have ht : p2_39.t.Contains (quadraturePoint 2 39) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨39,by decide⟩).scale 1 12) = p2_39.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨39,by decide⟩
  have he : PointBox.calc p2_39.t = p2_39 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_40_contains : p2_40.Contains (quadraturePoint 2 40) := by
  have ht : p2_40.t.Contains (quadraturePoint 2 40) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨40,by decide⟩).scale 1 12) = p2_40.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨40,by decide⟩
  have he : PointBox.calc p2_40.t = p2_40 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_41_contains : p2_41.Contains (quadraturePoint 2 41) := by
  have ht : p2_41.t.Contains (quadraturePoint 2 41) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨41,by decide⟩).scale 1 12) = p2_41.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨41,by decide⟩
  have he : PointBox.calc p2_41.t = p2_41 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_42_contains : p2_42.Contains (quadraturePoint 2 42) := by
  have ht : p2_42.t.Contains (quadraturePoint 2 42) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨42,by decide⟩).scale 1 12) = p2_42.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨42,by decide⟩
  have he : PointBox.calc p2_42.t = p2_42 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_43_contains : p2_43.Contains (quadraturePoint 2 43) := by
  have ht : p2_43.t.Contains (quadraturePoint 2 43) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨43,by decide⟩).scale 1 12) = p2_43.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨43,by decide⟩
  have he : PointBox.calc p2_43.t = p2_43 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_44_contains : p2_44.Contains (quadraturePoint 2 44) := by
  have ht : p2_44.t.Contains (quadraturePoint 2 44) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨44,by decide⟩).scale 1 12) = p2_44.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨44,by decide⟩
  have he : PointBox.calc p2_44.t = p2_44 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_45_contains : p2_45.Contains (quadraturePoint 2 45) := by
  have ht : p2_45.t.Contains (quadraturePoint 2 45) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨45,by decide⟩).scale 1 12) = p2_45.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨45,by decide⟩
  have he : PointBox.calc p2_45.t = p2_45 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_46_contains : p2_46.Contains (quadraturePoint 2 46) := by
  have ht : p2_46.t.Contains (quadraturePoint 2 46) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨46,by decide⟩).scale 1 12) = p2_46.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨46,by decide⟩
  have he : PointBox.calc p2_46.t = p2_46 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_47_contains : p2_47.Contains (quadraturePoint 2 47) := by
  have ht : p2_47.t.Contains (quadraturePoint 2 47) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨47,by decide⟩).scale 1 12) = p2_47.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨47,by decide⟩
  have he : PointBox.calc p2_47.t = p2_47 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_48_contains : p2_48.Contains (quadraturePoint 2 48) := by
  have ht : p2_48.t.Contains (quadraturePoint 2 48) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p2_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨48,by decide⟩
  have he : PointBox.calc p2_48.t = p2_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_49_contains : p2_49.Contains (quadraturePoint 2 49) := by
  have ht : p2_49.t.Contains (quadraturePoint 2 49) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p2_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨49,by decide⟩
  have he : PointBox.calc p2_49.t = p2_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_50_contains : p2_50.Contains (quadraturePoint 2 50) := by
  have ht : p2_50.t.Contains (quadraturePoint 2 50) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p2_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨50,by decide⟩
  have he : PointBox.calc p2_50.t = p2_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_51_contains : p2_51.Contains (quadraturePoint 2 51) := by
  have ht : p2_51.t.Contains (quadraturePoint 2 51) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p2_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨51,by decide⟩
  have he : PointBox.calc p2_51.t = p2_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_52_contains : p2_52.Contains (quadraturePoint 2 52) := by
  have ht : p2_52.t.Contains (quadraturePoint 2 52) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p2_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨52,by decide⟩
  have he : PointBox.calc p2_52.t = p2_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_53_contains : p2_53.Contains (quadraturePoint 2 53) := by
  have ht : p2_53.t.Contains (quadraturePoint 2 53) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p2_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨53,by decide⟩
  have he : PointBox.calc p2_53.t = p2_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_54_contains : p2_54.Contains (quadraturePoint 2 54) := by
  have ht : p2_54.t.Contains (quadraturePoint 2 54) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p2_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨54,by decide⟩
  have he : PointBox.calc p2_54.t = p2_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_55_contains : p2_55.Contains (quadraturePoint 2 55) := by
  have ht : p2_55.t.Contains (quadraturePoint 2 55) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p2_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨55,by decide⟩
  have he : PointBox.calc p2_55.t = p2_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_56_contains : p2_56.Contains (quadraturePoint 2 56) := by
  have ht : p2_56.t.Contains (quadraturePoint 2 56) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p2_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨56,by decide⟩
  have he : PointBox.calc p2_56.t = p2_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_57_contains : p2_57.Contains (quadraturePoint 2 57) := by
  have ht : p2_57.t.Contains (quadraturePoint 2 57) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p2_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨57,by decide⟩
  have he : PointBox.calc p2_57.t = p2_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_58_contains : p2_58.Contains (quadraturePoint 2 58) := by
  have ht : p2_58.t.Contains (quadraturePoint 2 58) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p2_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨58,by decide⟩
  have he : PointBox.calc p2_58.t = p2_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_59_contains : p2_59.Contains (quadraturePoint 2 59) := by
  have ht : p2_59.t.Contains (quadraturePoint 2 59) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p2_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨59,by decide⟩
  have he : PointBox.calc p2_59.t = p2_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_60_contains : p2_60.Contains (quadraturePoint 2 60) := by
  have ht : p2_60.t.Contains (quadraturePoint 2 60) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p2_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨60,by decide⟩
  have he : PointBox.calc p2_60.t = p2_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_61_contains : p2_61.Contains (quadraturePoint 2 61) := by
  have ht : p2_61.t.Contains (quadraturePoint 2 61) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p2_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨61,by decide⟩
  have he : PointBox.calc p2_61.t = p2_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_62_contains : p2_62.Contains (quadraturePoint 2 62) := by
  have ht : p2_62.t.Contains (quadraturePoint 2 62) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p2_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨62,by decide⟩
  have he : PointBox.calc p2_62.t = p2_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_63_contains : p2_63.Contains (quadraturePoint 2 63) := by
  have ht : p2_63.t.Contains (quadraturePoint 2 63) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p2_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨63,by decide⟩
  have he : PointBox.calc p2_63.t = p2_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_64_contains : p2_64.Contains (quadraturePoint 2 64) := by
  have ht : p2_64.t.Contains (quadraturePoint 2 64) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p2_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨64,by decide⟩
  have he : PointBox.calc p2_64.t = p2_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_65_contains : p2_65.Contains (quadraturePoint 2 65) := by
  have ht : p2_65.t.Contains (quadraturePoint 2 65) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p2_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨65,by decide⟩
  have he : PointBox.calc p2_65.t = p2_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_66_contains : p2_66.Contains (quadraturePoint 2 66) := by
  have ht : p2_66.t.Contains (quadraturePoint 2 66) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p2_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨66,by decide⟩
  have he : PointBox.calc p2_66.t = p2_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_67_contains : p2_67.Contains (quadraturePoint 2 67) := by
  have ht : p2_67.t.Contains (quadraturePoint 2 67) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p2_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨67,by decide⟩
  have he : PointBox.calc p2_67.t = p2_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_68_contains : p2_68.Contains (quadraturePoint 2 68) := by
  have ht : p2_68.t.Contains (quadraturePoint 2 68) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p2_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨68,by decide⟩
  have he : PointBox.calc p2_68.t = p2_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_69_contains : p2_69.Contains (quadraturePoint 2 69) := by
  have ht : p2_69.t.Contains (quadraturePoint 2 69) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p2_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨69,by decide⟩
  have he : PointBox.calc p2_69.t = p2_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_70_contains : p2_70.Contains (quadraturePoint 2 70) := by
  have ht : p2_70.t.Contains (quadraturePoint 2 70) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p2_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨70,by decide⟩
  have he : PointBox.calc p2_70.t = p2_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_71_contains : p2_71.Contains (quadraturePoint 2 71) := by
  have ht : p2_71.t.Contains (quadraturePoint 2 71) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p2_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨71,by decide⟩
  have he : PointBox.calc p2_71.t = p2_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_72_contains : p2_72.Contains (quadraturePoint 2 72) := by
  have ht : p2_72.t.Contains (quadraturePoint 2 72) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p2_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨72,by decide⟩
  have he : PointBox.calc p2_72.t = p2_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_73_contains : p2_73.Contains (quadraturePoint 2 73) := by
  have ht : p2_73.t.Contains (quadraturePoint 2 73) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p2_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨73,by decide⟩
  have he : PointBox.calc p2_73.t = p2_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_74_contains : p2_74.Contains (quadraturePoint 2 74) := by
  have ht : p2_74.t.Contains (quadraturePoint 2 74) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p2_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨74,by decide⟩
  have he : PointBox.calc p2_74.t = p2_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_75_contains : p2_75.Contains (quadraturePoint 2 75) := by
  have ht : p2_75.t.Contains (quadraturePoint 2 75) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p2_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨75,by decide⟩
  have he : PointBox.calc p2_75.t = p2_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_76_contains : p2_76.Contains (quadraturePoint 2 76) := by
  have ht : p2_76.t.Contains (quadraturePoint 2 76) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p2_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨76,by decide⟩
  have he : PointBox.calc p2_76.t = p2_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_77_contains : p2_77.Contains (quadraturePoint 2 77) := by
  have ht : p2_77.t.Contains (quadraturePoint 2 77) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p2_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨77,by decide⟩
  have he : PointBox.calc p2_77.t = p2_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_78_contains : p2_78.Contains (quadraturePoint 2 78) := by
  have ht : p2_78.t.Contains (quadraturePoint 2 78) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p2_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨78,by decide⟩
  have he : PointBox.calc p2_78.t = p2_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_79_contains : p2_79.Contains (quadraturePoint 2 79) := by
  have ht : p2_79.t.Contains (quadraturePoint 2 79) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p2_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨79,by decide⟩
  have he : PointBox.calc p2_79.t = p2_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_80_contains : p2_80.Contains (quadraturePoint 2 80) := by
  have ht : p2_80.t.Contains (quadraturePoint 2 80) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p2_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨80,by decide⟩
  have he : PointBox.calc p2_80.t = p2_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_81_contains : p2_81.Contains (quadraturePoint 2 81) := by
  have ht : p2_81.t.Contains (quadraturePoint 2 81) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p2_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨81,by decide⟩
  have he : PointBox.calc p2_81.t = p2_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_82_contains : p2_82.Contains (quadraturePoint 2 82) := by
  have ht : p2_82.t.Contains (quadraturePoint 2 82) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p2_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨82,by decide⟩
  have he : PointBox.calc p2_82.t = p2_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_83_contains : p2_83.Contains (quadraturePoint 2 83) := by
  have ht : p2_83.t.Contains (quadraturePoint 2 83) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p2_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨83,by decide⟩
  have he : PointBox.calc p2_83.t = p2_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_84_contains : p2_84.Contains (quadraturePoint 2 84) := by
  have ht : p2_84.t.Contains (quadraturePoint 2 84) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p2_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨84,by decide⟩
  have he : PointBox.calc p2_84.t = p2_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_85_contains : p2_85.Contains (quadraturePoint 2 85) := by
  have ht : p2_85.t.Contains (quadraturePoint 2 85) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p2_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨85,by decide⟩
  have he : PointBox.calc p2_85.t = p2_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_86_contains : p2_86.Contains (quadraturePoint 2 86) := by
  have ht : p2_86.t.Contains (quadraturePoint 2 86) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p2_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨86,by decide⟩
  have he : PointBox.calc p2_86.t = p2_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_87_contains : p2_87.Contains (quadraturePoint 2 87) := by
  have ht : p2_87.t.Contains (quadraturePoint 2 87) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p2_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨87,by decide⟩
  have he : PointBox.calc p2_87.t = p2_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_88_contains : p2_88.Contains (quadraturePoint 2 88) := by
  have ht : p2_88.t.Contains (quadraturePoint 2 88) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p2_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨88,by decide⟩
  have he : PointBox.calc p2_88.t = p2_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_89_contains : p2_89.Contains (quadraturePoint 2 89) := by
  have ht : p2_89.t.Contains (quadraturePoint 2 89) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p2_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨89,by decide⟩
  have he : PointBox.calc p2_89.t = p2_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_90_contains : p2_90.Contains (quadraturePoint 2 90) := by
  have ht : p2_90.t.Contains (quadraturePoint 2 90) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p2_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨90,by decide⟩
  have he : PointBox.calc p2_90.t = p2_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_91_contains : p2_91.Contains (quadraturePoint 2 91) := by
  have ht : p2_91.t.Contains (quadraturePoint 2 91) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p2_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨91,by decide⟩
  have he : PointBox.calc p2_91.t = p2_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_92_contains : p2_92.Contains (quadraturePoint 2 92) := by
  have ht : p2_92.t.Contains (quadraturePoint 2 92) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p2_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨92,by decide⟩
  have he : PointBox.calc p2_92.t = p2_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_93_contains : p2_93.Contains (quadraturePoint 2 93) := by
  have ht : p2_93.t.Contains (quadraturePoint 2 93) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p2_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨93,by decide⟩
  have he : PointBox.calc p2_93.t = p2_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_94_contains : p2_94.Contains (quadraturePoint 2 94) := by
  have ht : p2_94.t.Contains (quadraturePoint 2 94) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p2_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨94,by decide⟩
  have he : PointBox.calc p2_94.t = p2_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_95_contains : p2_95.Contains (quadraturePoint 2 95) := by
  have ht : p2_95.t.Contains (quadraturePoint 2 95) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p2_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨95,by decide⟩
  have he : PointBox.calc p2_95.t = p2_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_96_contains : p2_96.Contains (quadraturePoint 2 96) := by
  have ht : p2_96.t.Contains (quadraturePoint 2 96) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨96,by decide⟩).scale 1 12) = p2_96.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨96,by decide⟩
  have he : PointBox.calc p2_96.t = p2_96 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_97_contains : p2_97.Contains (quadraturePoint 2 97) := by
  have ht : p2_97.t.Contains (quadraturePoint 2 97) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p2_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨97,by decide⟩
  have he : PointBox.calc p2_97.t = p2_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_98_contains : p2_98.Contains (quadraturePoint 2 98) := by
  have ht : p2_98.t.Contains (quadraturePoint 2 98) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨98,by decide⟩).scale 1 12) = p2_98.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨98,by decide⟩
  have he : PointBox.calc p2_98.t = p2_98 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_99_contains : p2_99.Contains (quadraturePoint 2 99) := by
  have ht : p2_99.t.Contains (quadraturePoint 2 99) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨99,by decide⟩).scale 1 12) = p2_99.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨99,by decide⟩
  have he : PointBox.calc p2_99.t = p2_99 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_100_contains : p2_100.Contains (quadraturePoint 2 100) := by
  have ht : p2_100.t.Contains (quadraturePoint 2 100) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨100,by decide⟩).scale 1 12) = p2_100.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨100,by decide⟩
  have he : PointBox.calc p2_100.t = p2_100 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_101_contains : p2_101.Contains (quadraturePoint 2 101) := by
  have ht : p2_101.t.Contains (quadraturePoint 2 101) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨101,by decide⟩).scale 1 12) = p2_101.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨101,by decide⟩
  have he : PointBox.calc p2_101.t = p2_101 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_102_contains : p2_102.Contains (quadraturePoint 2 102) := by
  have ht : p2_102.t.Contains (quadraturePoint 2 102) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨102,by decide⟩).scale 1 12) = p2_102.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨102,by decide⟩
  have he : PointBox.calc p2_102.t = p2_102 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_103_contains : p2_103.Contains (quadraturePoint 2 103) := by
  have ht : p2_103.t.Contains (quadraturePoint 2 103) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨103,by decide⟩).scale 1 12) = p2_103.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨103,by decide⟩
  have he : PointBox.calc p2_103.t = p2_103 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_104_contains : p2_104.Contains (quadraturePoint 2 104) := by
  have ht : p2_104.t.Contains (quadraturePoint 2 104) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨104,by decide⟩).scale 1 12) = p2_104.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨104,by decide⟩
  have he : PointBox.calc p2_104.t = p2_104 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_105_contains : p2_105.Contains (quadraturePoint 2 105) := by
  have ht : p2_105.t.Contains (quadraturePoint 2 105) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨105,by decide⟩).scale 1 12) = p2_105.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨105,by decide⟩
  have he : PointBox.calc p2_105.t = p2_105 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_106_contains : p2_106.Contains (quadraturePoint 2 106) := by
  have ht : p2_106.t.Contains (quadraturePoint 2 106) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨106,by decide⟩).scale 1 12) = p2_106.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨106,by decide⟩
  have he : PointBox.calc p2_106.t = p2_106 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_107_contains : p2_107.Contains (quadraturePoint 2 107) := by
  have ht : p2_107.t.Contains (quadraturePoint 2 107) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨107,by decide⟩).scale 1 12) = p2_107.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨107,by decide⟩
  have he : PointBox.calc p2_107.t = p2_107 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_108_contains : p2_108.Contains (quadraturePoint 2 108) := by
  have ht : p2_108.t.Contains (quadraturePoint 2 108) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨108,by decide⟩).scale 1 12) = p2_108.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨108,by decide⟩
  have he : PointBox.calc p2_108.t = p2_108 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_109_contains : p2_109.Contains (quadraturePoint 2 109) := by
  have ht : p2_109.t.Contains (quadraturePoint 2 109) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨109,by decide⟩).scale 1 12) = p2_109.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨109,by decide⟩
  have he : PointBox.calc p2_109.t = p2_109 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_110_contains : p2_110.Contains (quadraturePoint 2 110) := by
  have ht : p2_110.t.Contains (quadraturePoint 2 110) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨110,by decide⟩).scale 1 12) = p2_110.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨110,by decide⟩
  have he : PointBox.calc p2_110.t = p2_110 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_111_contains : p2_111.Contains (quadraturePoint 2 111) := by
  have ht : p2_111.t.Contains (quadraturePoint 2 111) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨111,by decide⟩).scale 1 12) = p2_111.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨111,by decide⟩
  have he : PointBox.calc p2_111.t = p2_111 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_144_contains : p2_144.Contains (quadraturePoint 2 144) := by
  have ht : p2_144.t.Contains (quadraturePoint 2 144) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨144,by decide⟩).scale 1 12) = p2_144.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨144,by decide⟩
  have he : PointBox.calc p2_144.t = p2_144 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_145_contains : p2_145.Contains (quadraturePoint 2 145) := by
  have ht : p2_145.t.Contains (quadraturePoint 2 145) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨145,by decide⟩).scale 1 12) = p2_145.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨145,by decide⟩
  have he : PointBox.calc p2_145.t = p2_145 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_146_contains : p2_146.Contains (quadraturePoint 2 146) := by
  have ht : p2_146.t.Contains (quadraturePoint 2 146) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨146,by decide⟩).scale 1 12) = p2_146.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨146,by decide⟩
  have he : PointBox.calc p2_146.t = p2_146 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_147_contains : p2_147.Contains (quadraturePoint 2 147) := by
  have ht : p2_147.t.Contains (quadraturePoint 2 147) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨147,by decide⟩).scale 1 12) = p2_147.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨147,by decide⟩
  have he : PointBox.calc p2_147.t = p2_147 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_148_contains : p2_148.Contains (quadraturePoint 2 148) := by
  have ht : p2_148.t.Contains (quadraturePoint 2 148) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨148,by decide⟩).scale 1 12) = p2_148.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨148,by decide⟩
  have he : PointBox.calc p2_148.t = p2_148 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_149_contains : p2_149.Contains (quadraturePoint 2 149) := by
  have ht : p2_149.t.Contains (quadraturePoint 2 149) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨149,by decide⟩).scale 1 12) = p2_149.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨149,by decide⟩
  have he : PointBox.calc p2_149.t = p2_149 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_150_contains : p2_150.Contains (quadraturePoint 2 150) := by
  have ht : p2_150.t.Contains (quadraturePoint 2 150) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨150,by decide⟩).scale 1 12) = p2_150.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨150,by decide⟩
  have he : PointBox.calc p2_150.t = p2_150 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_151_contains : p2_151.Contains (quadraturePoint 2 151) := by
  have ht : p2_151.t.Contains (quadraturePoint 2 151) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨151,by decide⟩).scale 1 12) = p2_151.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨151,by decide⟩
  have he : PointBox.calc p2_151.t = p2_151 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_152_contains : p2_152.Contains (quadraturePoint 2 152) := by
  have ht : p2_152.t.Contains (quadraturePoint 2 152) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨152,by decide⟩).scale 1 12) = p2_152.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨152,by decide⟩
  have he : PointBox.calc p2_152.t = p2_152 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_153_contains : p2_153.Contains (quadraturePoint 2 153) := by
  have ht : p2_153.t.Contains (quadraturePoint 2 153) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨153,by decide⟩).scale 1 12) = p2_153.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨153,by decide⟩
  have he : PointBox.calc p2_153.t = p2_153 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_154_contains : p2_154.Contains (quadraturePoint 2 154) := by
  have ht : p2_154.t.Contains (quadraturePoint 2 154) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨154,by decide⟩).scale 1 12) = p2_154.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨154,by decide⟩
  have he : PointBox.calc p2_154.t = p2_154 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_155_contains : p2_155.Contains (quadraturePoint 2 155) := by
  have ht : p2_155.t.Contains (quadraturePoint 2 155) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨155,by decide⟩).scale 1 12) = p2_155.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨155,by decide⟩
  have he : PointBox.calc p2_155.t = p2_155 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_156_contains : p2_156.Contains (quadraturePoint 2 156) := by
  have ht : p2_156.t.Contains (quadraturePoint 2 156) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨156,by decide⟩).scale 1 12) = p2_156.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨156,by decide⟩
  have he : PointBox.calc p2_156.t = p2_156 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_157_contains : p2_157.Contains (quadraturePoint 2 157) := by
  have ht : p2_157.t.Contains (quadraturePoint 2 157) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨157,by decide⟩).scale 1 12) = p2_157.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨157,by decide⟩
  have he : PointBox.calc p2_157.t = p2_157 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_158_contains : p2_158.Contains (quadraturePoint 2 158) := by
  have ht : p2_158.t.Contains (quadraturePoint 2 158) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨158,by decide⟩).scale 1 12) = p2_158.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨158,by decide⟩
  have he : PointBox.calc p2_158.t = p2_158 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_159_contains : p2_159.Contains (quadraturePoint 2 159) := by
  have ht : p2_159.t.Contains (quadraturePoint 2 159) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨159,by decide⟩).scale 1 12) = p2_159.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨159,by decide⟩
  have he : PointBox.calc p2_159.t = p2_159 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_224_contains : p2_224.Contains (quadraturePoint 2 224) := by
  have ht : p2_224.t.Contains (quadraturePoint 2 224) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p2_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨224,by decide⟩
  have he : PointBox.calc p2_224.t = p2_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_225_contains : p2_225.Contains (quadraturePoint 2 225) := by
  have ht : p2_225.t.Contains (quadraturePoint 2 225) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p2_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨225,by decide⟩
  have he : PointBox.calc p2_225.t = p2_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_226_contains : p2_226.Contains (quadraturePoint 2 226) := by
  have ht : p2_226.t.Contains (quadraturePoint 2 226) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p2_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨226,by decide⟩
  have he : PointBox.calc p2_226.t = p2_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_227_contains : p2_227.Contains (quadraturePoint 2 227) := by
  have ht : p2_227.t.Contains (quadraturePoint 2 227) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p2_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨227,by decide⟩
  have he : PointBox.calc p2_227.t = p2_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_228_contains : p2_228.Contains (quadraturePoint 2 228) := by
  have ht : p2_228.t.Contains (quadraturePoint 2 228) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p2_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨228,by decide⟩
  have he : PointBox.calc p2_228.t = p2_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_229_contains : p2_229.Contains (quadraturePoint 2 229) := by
  have ht : p2_229.t.Contains (quadraturePoint 2 229) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p2_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨229,by decide⟩
  have he : PointBox.calc p2_229.t = p2_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_230_contains : p2_230.Contains (quadraturePoint 2 230) := by
  have ht : p2_230.t.Contains (quadraturePoint 2 230) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p2_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨230,by decide⟩
  have he : PointBox.calc p2_230.t = p2_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_231_contains : p2_231.Contains (quadraturePoint 2 231) := by
  have ht : p2_231.t.Contains (quadraturePoint 2 231) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p2_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨231,by decide⟩
  have he : PointBox.calc p2_231.t = p2_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_232_contains : p2_232.Contains (quadraturePoint 2 232) := by
  have ht : p2_232.t.Contains (quadraturePoint 2 232) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p2_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨232,by decide⟩
  have he : PointBox.calc p2_232.t = p2_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_233_contains : p2_233.Contains (quadraturePoint 2 233) := by
  have ht : p2_233.t.Contains (quadraturePoint 2 233) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p2_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨233,by decide⟩
  have he : PointBox.calc p2_233.t = p2_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_234_contains : p2_234.Contains (quadraturePoint 2 234) := by
  have ht : p2_234.t.Contains (quadraturePoint 2 234) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p2_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨234,by decide⟩
  have he : PointBox.calc p2_234.t = p2_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_235_contains : p2_235.Contains (quadraturePoint 2 235) := by
  have ht : p2_235.t.Contains (quadraturePoint 2 235) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p2_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨235,by decide⟩
  have he : PointBox.calc p2_235.t = p2_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_236_contains : p2_236.Contains (quadraturePoint 2 236) := by
  have ht : p2_236.t.Contains (quadraturePoint 2 236) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p2_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨236,by decide⟩
  have he : PointBox.calc p2_236.t = p2_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_237_contains : p2_237.Contains (quadraturePoint 2 237) := by
  have ht : p2_237.t.Contains (quadraturePoint 2 237) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p2_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨237,by decide⟩
  have he : PointBox.calc p2_237.t = p2_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_238_contains : p2_238.Contains (quadraturePoint 2 238) := by
  have ht : p2_238.t.Contains (quadraturePoint 2 238) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p2_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨238,by decide⟩
  have he : PointBox.calc p2_238.t = p2_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p2_239_contains : p2_239.Contains (quadraturePoint 2 239) := by
  have ht : p2_239.t.Contains (quadraturePoint 2 239) := by
    have he : (RBox.rat 5 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p2_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 2 ⟨239,by decide⟩
  have he : PointBox.calc p2_239.t = p2_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row2_0_contains (k : Fin 16) : (row2_0 k).Contains (quadraturePoint 2 (0+k.val)) := by
  fin_cases k
  · exact p2_0_contains
  · exact p2_1_contains
  · exact p2_2_contains
  · exact p2_3_contains
  · exact p2_4_contains
  · exact p2_5_contains
  · exact p2_6_contains
  · exact p2_7_contains
  · exact p2_8_contains
  · exact p2_9_contains
  · exact p2_10_contains
  · exact p2_11_contains
  · exact p2_12_contains
  · exact p2_13_contains
  · exact p2_14_contains
  · exact p2_15_contains
lemma row2_1_contains (k : Fin 16) : (row2_1 k).Contains (quadraturePoint 2 (16+k.val)) := by
  fin_cases k
  · exact p2_16_contains
  · exact p2_17_contains
  · exact p2_18_contains
  · exact p2_19_contains
  · exact p2_20_contains
  · exact p2_21_contains
  · exact p2_22_contains
  · exact p2_23_contains
  · exact p2_24_contains
  · exact p2_25_contains
  · exact p2_26_contains
  · exact p2_27_contains
  · exact p2_28_contains
  · exact p2_29_contains
  · exact p2_30_contains
  · exact p2_31_contains
lemma row2_2_contains (k : Fin 16) : (row2_2 k).Contains (quadraturePoint 2 (32+k.val)) := by
  fin_cases k
  · exact p2_32_contains
  · exact p2_33_contains
  · exact p2_34_contains
  · exact p2_35_contains
  · exact p2_36_contains
  · exact p2_37_contains
  · exact p2_38_contains
  · exact p2_39_contains
  · exact p2_40_contains
  · exact p2_41_contains
  · exact p2_42_contains
  · exact p2_43_contains
  · exact p2_44_contains
  · exact p2_45_contains
  · exact p2_46_contains
  · exact p2_47_contains
lemma row2_3_contains (k : Fin 16) : (row2_3 k).Contains (quadraturePoint 2 (48+k.val)) := by
  fin_cases k
  · exact p2_48_contains
  · exact p2_49_contains
  · exact p2_50_contains
  · exact p2_51_contains
  · exact p2_52_contains
  · exact p2_53_contains
  · exact p2_54_contains
  · exact p2_55_contains
  · exact p2_56_contains
  · exact p2_57_contains
  · exact p2_58_contains
  · exact p2_59_contains
  · exact p2_60_contains
  · exact p2_61_contains
  · exact p2_62_contains
  · exact p2_63_contains
lemma row2_4_contains (k : Fin 16) : (row2_4 k).Contains (quadraturePoint 2 (64+k.val)) := by
  fin_cases k
  · exact p2_64_contains
  · exact p2_65_contains
  · exact p2_66_contains
  · exact p2_67_contains
  · exact p2_68_contains
  · exact p2_69_contains
  · exact p2_70_contains
  · exact p2_71_contains
  · exact p2_72_contains
  · exact p2_73_contains
  · exact p2_74_contains
  · exact p2_75_contains
  · exact p2_76_contains
  · exact p2_77_contains
  · exact p2_78_contains
  · exact p2_79_contains
lemma row2_5_contains (k : Fin 16) : (row2_5 k).Contains (quadraturePoint 2 (80+k.val)) := by
  fin_cases k
  · exact p2_80_contains
  · exact p2_81_contains
  · exact p2_82_contains
  · exact p2_83_contains
  · exact p2_84_contains
  · exact p2_85_contains
  · exact p2_86_contains
  · exact p2_87_contains
  · exact p2_88_contains
  · exact p2_89_contains
  · exact p2_90_contains
  · exact p2_91_contains
  · exact p2_92_contains
  · exact p2_93_contains
  · exact p2_94_contains
  · exact p2_95_contains
lemma row2_6_contains (k : Fin 16) : (row2_6 k).Contains (quadraturePoint 2 (96+k.val)) := by
  fin_cases k
  · exact p2_96_contains
  · exact p2_97_contains
  · exact p2_98_contains
  · exact p2_99_contains
  · exact p2_100_contains
  · exact p2_101_contains
  · exact p2_102_contains
  · exact p2_103_contains
  · exact p2_104_contains
  · exact p2_105_contains
  · exact p2_106_contains
  · exact p2_107_contains
  · exact p2_108_contains
  · exact p2_109_contains
  · exact p2_110_contains
  · exact p2_111_contains
lemma row2_9_contains (k : Fin 16) : (row2_9 k).Contains (quadraturePoint 2 (144+k.val)) := by
  fin_cases k
  · exact p2_144_contains
  · exact p2_145_contains
  · exact p2_146_contains
  · exact p2_147_contains
  · exact p2_148_contains
  · exact p2_149_contains
  · exact p2_150_contains
  · exact p2_151_contains
  · exact p2_152_contains
  · exact p2_153_contains
  · exact p2_154_contains
  · exact p2_155_contains
  · exact p2_156_contains
  · exact p2_157_contains
  · exact p2_158_contains
  · exact p2_159_contains
lemma row2_14_contains (k : Fin 16) : (row2_14 k).Contains (quadraturePoint 2 (224+k.val)) := by
  fin_cases k
  · exact p2_224_contains
  · exact p2_225_contains
  · exact p2_226_contains
  · exact p2_227_contains
  · exact p2_228_contains
  · exact p2_229_contains
  · exact p2_230_contains
  · exact p2_231_contains
  · exact p2_232_contains
  · exact p2_233_contains
  · exact p2_234_contains
  · exact p2_235_contains
  · exact p2_236_contains
  · exact p2_237_contains
  · exact p2_238_contains
  · exact p2_239_contains
lemma row2_contains_g_oai (i k : Fin 16) : (row2 i k).Contains (quadraturePoint 2 (16*i.val+k.val)) := by
  fin_cases i
  · exact row2_0_contains k
  · exact row2_1_contains k
  · exact row2_2_contains k
  · exact row2_3_contains k
  · exact row2_4_contains k
  · exact row2_5_contains k
  · exact row2_6_contains k
  · exact row2_7_contains_g k
  · exact row2_8_contains_g k
  · exact row2_9_contains k
  · exact row2_10_contains_g k
  · exact row2_11_contains_g k
  · exact row2_12_contains_g k
  · exact row2_13_contains_g k
  · exact row2_14_contains k
  · exact row2_15_contains_g k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row2_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row2_contains_g_oai
