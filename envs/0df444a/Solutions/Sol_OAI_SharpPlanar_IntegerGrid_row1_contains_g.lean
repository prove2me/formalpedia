-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:07.538933+00:00
-- url     : https://prove2.me/submissions/1cf2afed-d707-4b2b-9dcc-e090aeb881a9

import Mathlib
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_14_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_9_contains_g
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

lemma p1_0_contains : p1_0.Contains (quadraturePoint 1 0) := by
  have ht : p1_0.t.Contains (quadraturePoint 1 0) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p1_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨0,by decide⟩
  have he : PointBox.calc p1_0.t = p1_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_1_contains : p1_1.Contains (quadraturePoint 1 1) := by
  have ht : p1_1.t.Contains (quadraturePoint 1 1) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p1_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨1,by decide⟩
  have he : PointBox.calc p1_1.t = p1_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_2_contains : p1_2.Contains (quadraturePoint 1 2) := by
  have ht : p1_2.t.Contains (quadraturePoint 1 2) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p1_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨2,by decide⟩
  have he : PointBox.calc p1_2.t = p1_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_3_contains : p1_3.Contains (quadraturePoint 1 3) := by
  have ht : p1_3.t.Contains (quadraturePoint 1 3) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p1_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨3,by decide⟩
  have he : PointBox.calc p1_3.t = p1_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_4_contains : p1_4.Contains (quadraturePoint 1 4) := by
  have ht : p1_4.t.Contains (quadraturePoint 1 4) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p1_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨4,by decide⟩
  have he : PointBox.calc p1_4.t = p1_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_5_contains : p1_5.Contains (quadraturePoint 1 5) := by
  have ht : p1_5.t.Contains (quadraturePoint 1 5) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p1_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨5,by decide⟩
  have he : PointBox.calc p1_5.t = p1_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_6_contains : p1_6.Contains (quadraturePoint 1 6) := by
  have ht : p1_6.t.Contains (quadraturePoint 1 6) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p1_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨6,by decide⟩
  have he : PointBox.calc p1_6.t = p1_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_7_contains : p1_7.Contains (quadraturePoint 1 7) := by
  have ht : p1_7.t.Contains (quadraturePoint 1 7) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p1_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨7,by decide⟩
  have he : PointBox.calc p1_7.t = p1_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_8_contains : p1_8.Contains (quadraturePoint 1 8) := by
  have ht : p1_8.t.Contains (quadraturePoint 1 8) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p1_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨8,by decide⟩
  have he : PointBox.calc p1_8.t = p1_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_9_contains : p1_9.Contains (quadraturePoint 1 9) := by
  have ht : p1_9.t.Contains (quadraturePoint 1 9) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p1_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨9,by decide⟩
  have he : PointBox.calc p1_9.t = p1_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_10_contains : p1_10.Contains (quadraturePoint 1 10) := by
  have ht : p1_10.t.Contains (quadraturePoint 1 10) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p1_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨10,by decide⟩
  have he : PointBox.calc p1_10.t = p1_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_11_contains : p1_11.Contains (quadraturePoint 1 11) := by
  have ht : p1_11.t.Contains (quadraturePoint 1 11) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p1_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨11,by decide⟩
  have he : PointBox.calc p1_11.t = p1_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_12_contains : p1_12.Contains (quadraturePoint 1 12) := by
  have ht : p1_12.t.Contains (quadraturePoint 1 12) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p1_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨12,by decide⟩
  have he : PointBox.calc p1_12.t = p1_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_13_contains : p1_13.Contains (quadraturePoint 1 13) := by
  have ht : p1_13.t.Contains (quadraturePoint 1 13) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p1_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨13,by decide⟩
  have he : PointBox.calc p1_13.t = p1_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_14_contains : p1_14.Contains (quadraturePoint 1 14) := by
  have ht : p1_14.t.Contains (quadraturePoint 1 14) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p1_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨14,by decide⟩
  have he : PointBox.calc p1_14.t = p1_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_15_contains : p1_15.Contains (quadraturePoint 1 15) := by
  have ht : p1_15.t.Contains (quadraturePoint 1 15) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p1_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨15,by decide⟩
  have he : PointBox.calc p1_15.t = p1_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_48_contains : p1_48.Contains (quadraturePoint 1 48) := by
  have ht : p1_48.t.Contains (quadraturePoint 1 48) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p1_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨48,by decide⟩
  have he : PointBox.calc p1_48.t = p1_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_49_contains : p1_49.Contains (quadraturePoint 1 49) := by
  have ht : p1_49.t.Contains (quadraturePoint 1 49) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p1_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨49,by decide⟩
  have he : PointBox.calc p1_49.t = p1_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_50_contains : p1_50.Contains (quadraturePoint 1 50) := by
  have ht : p1_50.t.Contains (quadraturePoint 1 50) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p1_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨50,by decide⟩
  have he : PointBox.calc p1_50.t = p1_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_51_contains : p1_51.Contains (quadraturePoint 1 51) := by
  have ht : p1_51.t.Contains (quadraturePoint 1 51) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p1_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨51,by decide⟩
  have he : PointBox.calc p1_51.t = p1_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_52_contains : p1_52.Contains (quadraturePoint 1 52) := by
  have ht : p1_52.t.Contains (quadraturePoint 1 52) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p1_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨52,by decide⟩
  have he : PointBox.calc p1_52.t = p1_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_53_contains : p1_53.Contains (quadraturePoint 1 53) := by
  have ht : p1_53.t.Contains (quadraturePoint 1 53) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p1_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨53,by decide⟩
  have he : PointBox.calc p1_53.t = p1_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_54_contains : p1_54.Contains (quadraturePoint 1 54) := by
  have ht : p1_54.t.Contains (quadraturePoint 1 54) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p1_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨54,by decide⟩
  have he : PointBox.calc p1_54.t = p1_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_55_contains : p1_55.Contains (quadraturePoint 1 55) := by
  have ht : p1_55.t.Contains (quadraturePoint 1 55) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p1_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨55,by decide⟩
  have he : PointBox.calc p1_55.t = p1_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_56_contains : p1_56.Contains (quadraturePoint 1 56) := by
  have ht : p1_56.t.Contains (quadraturePoint 1 56) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p1_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨56,by decide⟩
  have he : PointBox.calc p1_56.t = p1_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_57_contains : p1_57.Contains (quadraturePoint 1 57) := by
  have ht : p1_57.t.Contains (quadraturePoint 1 57) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p1_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨57,by decide⟩
  have he : PointBox.calc p1_57.t = p1_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_58_contains : p1_58.Contains (quadraturePoint 1 58) := by
  have ht : p1_58.t.Contains (quadraturePoint 1 58) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p1_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨58,by decide⟩
  have he : PointBox.calc p1_58.t = p1_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_59_contains : p1_59.Contains (quadraturePoint 1 59) := by
  have ht : p1_59.t.Contains (quadraturePoint 1 59) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p1_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨59,by decide⟩
  have he : PointBox.calc p1_59.t = p1_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_60_contains : p1_60.Contains (quadraturePoint 1 60) := by
  have ht : p1_60.t.Contains (quadraturePoint 1 60) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p1_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨60,by decide⟩
  have he : PointBox.calc p1_60.t = p1_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_61_contains : p1_61.Contains (quadraturePoint 1 61) := by
  have ht : p1_61.t.Contains (quadraturePoint 1 61) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p1_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨61,by decide⟩
  have he : PointBox.calc p1_61.t = p1_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_62_contains : p1_62.Contains (quadraturePoint 1 62) := by
  have ht : p1_62.t.Contains (quadraturePoint 1 62) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p1_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨62,by decide⟩
  have he : PointBox.calc p1_62.t = p1_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_63_contains : p1_63.Contains (quadraturePoint 1 63) := by
  have ht : p1_63.t.Contains (quadraturePoint 1 63) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p1_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨63,by decide⟩
  have he : PointBox.calc p1_63.t = p1_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_64_contains : p1_64.Contains (quadraturePoint 1 64) := by
  have ht : p1_64.t.Contains (quadraturePoint 1 64) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p1_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨64,by decide⟩
  have he : PointBox.calc p1_64.t = p1_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_65_contains : p1_65.Contains (quadraturePoint 1 65) := by
  have ht : p1_65.t.Contains (quadraturePoint 1 65) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p1_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨65,by decide⟩
  have he : PointBox.calc p1_65.t = p1_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_66_contains : p1_66.Contains (quadraturePoint 1 66) := by
  have ht : p1_66.t.Contains (quadraturePoint 1 66) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p1_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨66,by decide⟩
  have he : PointBox.calc p1_66.t = p1_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_67_contains : p1_67.Contains (quadraturePoint 1 67) := by
  have ht : p1_67.t.Contains (quadraturePoint 1 67) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p1_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨67,by decide⟩
  have he : PointBox.calc p1_67.t = p1_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_68_contains : p1_68.Contains (quadraturePoint 1 68) := by
  have ht : p1_68.t.Contains (quadraturePoint 1 68) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p1_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨68,by decide⟩
  have he : PointBox.calc p1_68.t = p1_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_69_contains : p1_69.Contains (quadraturePoint 1 69) := by
  have ht : p1_69.t.Contains (quadraturePoint 1 69) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p1_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨69,by decide⟩
  have he : PointBox.calc p1_69.t = p1_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_70_contains : p1_70.Contains (quadraturePoint 1 70) := by
  have ht : p1_70.t.Contains (quadraturePoint 1 70) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p1_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨70,by decide⟩
  have he : PointBox.calc p1_70.t = p1_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_71_contains : p1_71.Contains (quadraturePoint 1 71) := by
  have ht : p1_71.t.Contains (quadraturePoint 1 71) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p1_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨71,by decide⟩
  have he : PointBox.calc p1_71.t = p1_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_72_contains : p1_72.Contains (quadraturePoint 1 72) := by
  have ht : p1_72.t.Contains (quadraturePoint 1 72) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p1_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨72,by decide⟩
  have he : PointBox.calc p1_72.t = p1_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_73_contains : p1_73.Contains (quadraturePoint 1 73) := by
  have ht : p1_73.t.Contains (quadraturePoint 1 73) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p1_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨73,by decide⟩
  have he : PointBox.calc p1_73.t = p1_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_74_contains : p1_74.Contains (quadraturePoint 1 74) := by
  have ht : p1_74.t.Contains (quadraturePoint 1 74) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p1_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨74,by decide⟩
  have he : PointBox.calc p1_74.t = p1_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_75_contains : p1_75.Contains (quadraturePoint 1 75) := by
  have ht : p1_75.t.Contains (quadraturePoint 1 75) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p1_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨75,by decide⟩
  have he : PointBox.calc p1_75.t = p1_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_76_contains : p1_76.Contains (quadraturePoint 1 76) := by
  have ht : p1_76.t.Contains (quadraturePoint 1 76) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p1_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨76,by decide⟩
  have he : PointBox.calc p1_76.t = p1_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_77_contains : p1_77.Contains (quadraturePoint 1 77) := by
  have ht : p1_77.t.Contains (quadraturePoint 1 77) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p1_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨77,by decide⟩
  have he : PointBox.calc p1_77.t = p1_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_78_contains : p1_78.Contains (quadraturePoint 1 78) := by
  have ht : p1_78.t.Contains (quadraturePoint 1 78) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p1_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨78,by decide⟩
  have he : PointBox.calc p1_78.t = p1_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_79_contains : p1_79.Contains (quadraturePoint 1 79) := by
  have ht : p1_79.t.Contains (quadraturePoint 1 79) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p1_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨79,by decide⟩
  have he : PointBox.calc p1_79.t = p1_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_80_contains : p1_80.Contains (quadraturePoint 1 80) := by
  have ht : p1_80.t.Contains (quadraturePoint 1 80) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p1_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨80,by decide⟩
  have he : PointBox.calc p1_80.t = p1_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_81_contains : p1_81.Contains (quadraturePoint 1 81) := by
  have ht : p1_81.t.Contains (quadraturePoint 1 81) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p1_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨81,by decide⟩
  have he : PointBox.calc p1_81.t = p1_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_82_contains : p1_82.Contains (quadraturePoint 1 82) := by
  have ht : p1_82.t.Contains (quadraturePoint 1 82) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p1_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨82,by decide⟩
  have he : PointBox.calc p1_82.t = p1_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_83_contains : p1_83.Contains (quadraturePoint 1 83) := by
  have ht : p1_83.t.Contains (quadraturePoint 1 83) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p1_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨83,by decide⟩
  have he : PointBox.calc p1_83.t = p1_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_84_contains : p1_84.Contains (quadraturePoint 1 84) := by
  have ht : p1_84.t.Contains (quadraturePoint 1 84) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p1_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨84,by decide⟩
  have he : PointBox.calc p1_84.t = p1_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_85_contains : p1_85.Contains (quadraturePoint 1 85) := by
  have ht : p1_85.t.Contains (quadraturePoint 1 85) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p1_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨85,by decide⟩
  have he : PointBox.calc p1_85.t = p1_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_86_contains : p1_86.Contains (quadraturePoint 1 86) := by
  have ht : p1_86.t.Contains (quadraturePoint 1 86) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p1_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨86,by decide⟩
  have he : PointBox.calc p1_86.t = p1_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_87_contains : p1_87.Contains (quadraturePoint 1 87) := by
  have ht : p1_87.t.Contains (quadraturePoint 1 87) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p1_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨87,by decide⟩
  have he : PointBox.calc p1_87.t = p1_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_88_contains : p1_88.Contains (quadraturePoint 1 88) := by
  have ht : p1_88.t.Contains (quadraturePoint 1 88) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p1_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨88,by decide⟩
  have he : PointBox.calc p1_88.t = p1_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_89_contains : p1_89.Contains (quadraturePoint 1 89) := by
  have ht : p1_89.t.Contains (quadraturePoint 1 89) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p1_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨89,by decide⟩
  have he : PointBox.calc p1_89.t = p1_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_90_contains : p1_90.Contains (quadraturePoint 1 90) := by
  have ht : p1_90.t.Contains (quadraturePoint 1 90) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p1_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨90,by decide⟩
  have he : PointBox.calc p1_90.t = p1_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_91_contains : p1_91.Contains (quadraturePoint 1 91) := by
  have ht : p1_91.t.Contains (quadraturePoint 1 91) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p1_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨91,by decide⟩
  have he : PointBox.calc p1_91.t = p1_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_92_contains : p1_92.Contains (quadraturePoint 1 92) := by
  have ht : p1_92.t.Contains (quadraturePoint 1 92) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p1_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨92,by decide⟩
  have he : PointBox.calc p1_92.t = p1_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_93_contains : p1_93.Contains (quadraturePoint 1 93) := by
  have ht : p1_93.t.Contains (quadraturePoint 1 93) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p1_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨93,by decide⟩
  have he : PointBox.calc p1_93.t = p1_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_94_contains : p1_94.Contains (quadraturePoint 1 94) := by
  have ht : p1_94.t.Contains (quadraturePoint 1 94) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p1_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨94,by decide⟩
  have he : PointBox.calc p1_94.t = p1_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_95_contains : p1_95.Contains (quadraturePoint 1 95) := by
  have ht : p1_95.t.Contains (quadraturePoint 1 95) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p1_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨95,by decide⟩
  have he : PointBox.calc p1_95.t = p1_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_0_contains (k : Fin 16) : (row1_0 k).Contains (quadraturePoint 1 (0+k.val)) := by
  fin_cases k
  · exact p1_0_contains
  · exact p1_1_contains
  · exact p1_2_contains
  · exact p1_3_contains
  · exact p1_4_contains
  · exact p1_5_contains
  · exact p1_6_contains
  · exact p1_7_contains
  · exact p1_8_contains
  · exact p1_9_contains
  · exact p1_10_contains
  · exact p1_11_contains
  · exact p1_12_contains
  · exact p1_13_contains
  · exact p1_14_contains
  · exact p1_15_contains
lemma row1_3_contains (k : Fin 16) : (row1_3 k).Contains (quadraturePoint 1 (48+k.val)) := by
  fin_cases k
  · exact p1_48_contains
  · exact p1_49_contains
  · exact p1_50_contains
  · exact p1_51_contains
  · exact p1_52_contains
  · exact p1_53_contains
  · exact p1_54_contains
  · exact p1_55_contains
  · exact p1_56_contains
  · exact p1_57_contains
  · exact p1_58_contains
  · exact p1_59_contains
  · exact p1_60_contains
  · exact p1_61_contains
  · exact p1_62_contains
  · exact p1_63_contains
lemma row1_4_contains (k : Fin 16) : (row1_4 k).Contains (quadraturePoint 1 (64+k.val)) := by
  fin_cases k
  · exact p1_64_contains
  · exact p1_65_contains
  · exact p1_66_contains
  · exact p1_67_contains
  · exact p1_68_contains
  · exact p1_69_contains
  · exact p1_70_contains
  · exact p1_71_contains
  · exact p1_72_contains
  · exact p1_73_contains
  · exact p1_74_contains
  · exact p1_75_contains
  · exact p1_76_contains
  · exact p1_77_contains
  · exact p1_78_contains
  · exact p1_79_contains
lemma row1_5_contains (k : Fin 16) : (row1_5 k).Contains (quadraturePoint 1 (80+k.val)) := by
  fin_cases k
  · exact p1_80_contains
  · exact p1_81_contains
  · exact p1_82_contains
  · exact p1_83_contains
  · exact p1_84_contains
  · exact p1_85_contains
  · exact p1_86_contains
  · exact p1_87_contains
  · exact p1_88_contains
  · exact p1_89_contains
  · exact p1_90_contains
  · exact p1_91_contains
  · exact p1_92_contains
  · exact p1_93_contains
  · exact p1_94_contains
  · exact p1_95_contains
lemma row1_contains_g_oai (i k : Fin 16) : (row1 i k).Contains (quadraturePoint 1 (16*i.val+k.val)) := by
  fin_cases i
  · exact row1_0_contains k
  · exact row1_1_contains_g k
  · exact row1_2_contains_g k
  · exact row1_3_contains k
  · exact row1_4_contains k
  · exact row1_5_contains k
  · exact row1_6_contains_g k
  · exact row1_7_contains_g k
  · exact row1_8_contains_g k
  · exact row1_9_contains_g k
  · exact row1_10_contains_g k
  · exact row1_11_contains_g k
  · exact row1_12_contains_g k
  · exact row1_13_contains_g k
  · exact row1_14_contains_g k
  · exact row1_15_contains_g k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_contains_g_oai
