-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.gridRows_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T08:38:06.112511+00:00
-- url     : https://prove2.me/submissions/28c77e8f-8937-48cf-8200-2e945ffb1763

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_rootRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row0_9_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_row5_contains_g
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

lemma p0_0_contains : p0_0.Contains (quadraturePoint 0 0) := by
  have ht : p0_0.t.Contains (quadraturePoint 0 0) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨0,by decide⟩).scale 1 12) = p0_0.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨0,by decide⟩
  have he : PointBox.calc p0_0.t = p0_0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_1_contains : p0_1.Contains (quadraturePoint 0 1) := by
  have ht : p0_1.t.Contains (quadraturePoint 0 1) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨1,by decide⟩).scale 1 12) = p0_1.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨1,by decide⟩
  have he : PointBox.calc p0_1.t = p0_1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_2_contains : p0_2.Contains (quadraturePoint 0 2) := by
  have ht : p0_2.t.Contains (quadraturePoint 0 2) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨2,by decide⟩).scale 1 12) = p0_2.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨2,by decide⟩
  have he : PointBox.calc p0_2.t = p0_2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_3_contains : p0_3.Contains (quadraturePoint 0 3) := by
  have ht : p0_3.t.Contains (quadraturePoint 0 3) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨3,by decide⟩).scale 1 12) = p0_3.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨3,by decide⟩
  have he : PointBox.calc p0_3.t = p0_3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_4_contains : p0_4.Contains (quadraturePoint 0 4) := by
  have ht : p0_4.t.Contains (quadraturePoint 0 4) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨4,by decide⟩).scale 1 12) = p0_4.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨4,by decide⟩
  have he : PointBox.calc p0_4.t = p0_4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_5_contains : p0_5.Contains (quadraturePoint 0 5) := by
  have ht : p0_5.t.Contains (quadraturePoint 0 5) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨5,by decide⟩).scale 1 12) = p0_5.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨5,by decide⟩
  have he : PointBox.calc p0_5.t = p0_5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_6_contains : p0_6.Contains (quadraturePoint 0 6) := by
  have ht : p0_6.t.Contains (quadraturePoint 0 6) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨6,by decide⟩).scale 1 12) = p0_6.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨6,by decide⟩
  have he : PointBox.calc p0_6.t = p0_6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_7_contains : p0_7.Contains (quadraturePoint 0 7) := by
  have ht : p0_7.t.Contains (quadraturePoint 0 7) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨7,by decide⟩).scale 1 12) = p0_7.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨7,by decide⟩
  have he : PointBox.calc p0_7.t = p0_7 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_8_contains : p0_8.Contains (quadraturePoint 0 8) := by
  have ht : p0_8.t.Contains (quadraturePoint 0 8) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨8,by decide⟩).scale 1 12) = p0_8.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨8,by decide⟩
  have he : PointBox.calc p0_8.t = p0_8 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_9_contains : p0_9.Contains (quadraturePoint 0 9) := by
  have ht : p0_9.t.Contains (quadraturePoint 0 9) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨9,by decide⟩).scale 1 12) = p0_9.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨9,by decide⟩
  have he : PointBox.calc p0_9.t = p0_9 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_10_contains : p0_10.Contains (quadraturePoint 0 10) := by
  have ht : p0_10.t.Contains (quadraturePoint 0 10) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨10,by decide⟩).scale 1 12) = p0_10.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨10,by decide⟩
  have he : PointBox.calc p0_10.t = p0_10 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_11_contains : p0_11.Contains (quadraturePoint 0 11) := by
  have ht : p0_11.t.Contains (quadraturePoint 0 11) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨11,by decide⟩).scale 1 12) = p0_11.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨11,by decide⟩
  have he : PointBox.calc p0_11.t = p0_11 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_12_contains : p0_12.Contains (quadraturePoint 0 12) := by
  have ht : p0_12.t.Contains (quadraturePoint 0 12) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨12,by decide⟩).scale 1 12) = p0_12.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨12,by decide⟩
  have he : PointBox.calc p0_12.t = p0_12 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_13_contains : p0_13.Contains (quadraturePoint 0 13) := by
  have ht : p0_13.t.Contains (quadraturePoint 0 13) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨13,by decide⟩).scale 1 12) = p0_13.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨13,by decide⟩
  have he : PointBox.calc p0_13.t = p0_13 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_14_contains : p0_14.Contains (quadraturePoint 0 14) := by
  have ht : p0_14.t.Contains (quadraturePoint 0 14) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨14,by decide⟩).scale 1 12) = p0_14.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨14,by decide⟩
  have he : PointBox.calc p0_14.t = p0_14 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_15_contains : p0_15.Contains (quadraturePoint 0 15) := by
  have ht : p0_15.t.Contains (quadraturePoint 0 15) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨15,by decide⟩).scale 1 12) = p0_15.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨15,by decide⟩
  have he : PointBox.calc p0_15.t = p0_15 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_80_contains : p0_80.Contains (quadraturePoint 0 80) := by
  have ht : p0_80.t.Contains (quadraturePoint 0 80) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨80,by decide⟩).scale 1 12) = p0_80.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨80,by decide⟩
  have he : PointBox.calc p0_80.t = p0_80 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_81_contains : p0_81.Contains (quadraturePoint 0 81) := by
  have ht : p0_81.t.Contains (quadraturePoint 0 81) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨81,by decide⟩).scale 1 12) = p0_81.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨81,by decide⟩
  have he : PointBox.calc p0_81.t = p0_81 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_82_contains : p0_82.Contains (quadraturePoint 0 82) := by
  have ht : p0_82.t.Contains (quadraturePoint 0 82) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨82,by decide⟩).scale 1 12) = p0_82.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨82,by decide⟩
  have he : PointBox.calc p0_82.t = p0_82 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_83_contains : p0_83.Contains (quadraturePoint 0 83) := by
  have ht : p0_83.t.Contains (quadraturePoint 0 83) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨83,by decide⟩).scale 1 12) = p0_83.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨83,by decide⟩
  have he : PointBox.calc p0_83.t = p0_83 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_84_contains : p0_84.Contains (quadraturePoint 0 84) := by
  have ht : p0_84.t.Contains (quadraturePoint 0 84) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨84,by decide⟩).scale 1 12) = p0_84.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨84,by decide⟩
  have he : PointBox.calc p0_84.t = p0_84 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_85_contains : p0_85.Contains (quadraturePoint 0 85) := by
  have ht : p0_85.t.Contains (quadraturePoint 0 85) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨85,by decide⟩).scale 1 12) = p0_85.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨85,by decide⟩
  have he : PointBox.calc p0_85.t = p0_85 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_86_contains : p0_86.Contains (quadraturePoint 0 86) := by
  have ht : p0_86.t.Contains (quadraturePoint 0 86) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨86,by decide⟩).scale 1 12) = p0_86.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨86,by decide⟩
  have he : PointBox.calc p0_86.t = p0_86 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_87_contains : p0_87.Contains (quadraturePoint 0 87) := by
  have ht : p0_87.t.Contains (quadraturePoint 0 87) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨87,by decide⟩).scale 1 12) = p0_87.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨87,by decide⟩
  have he : PointBox.calc p0_87.t = p0_87 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_88_contains : p0_88.Contains (quadraturePoint 0 88) := by
  have ht : p0_88.t.Contains (quadraturePoint 0 88) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨88,by decide⟩).scale 1 12) = p0_88.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨88,by decide⟩
  have he : PointBox.calc p0_88.t = p0_88 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_89_contains : p0_89.Contains (quadraturePoint 0 89) := by
  have ht : p0_89.t.Contains (quadraturePoint 0 89) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨89,by decide⟩).scale 1 12) = p0_89.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨89,by decide⟩
  have he : PointBox.calc p0_89.t = p0_89 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_90_contains : p0_90.Contains (quadraturePoint 0 90) := by
  have ht : p0_90.t.Contains (quadraturePoint 0 90) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨90,by decide⟩).scale 1 12) = p0_90.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨90,by decide⟩
  have he : PointBox.calc p0_90.t = p0_90 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_91_contains : p0_91.Contains (quadraturePoint 0 91) := by
  have ht : p0_91.t.Contains (quadraturePoint 0 91) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨91,by decide⟩).scale 1 12) = p0_91.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨91,by decide⟩
  have he : PointBox.calc p0_91.t = p0_91 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_92_contains : p0_92.Contains (quadraturePoint 0 92) := by
  have ht : p0_92.t.Contains (quadraturePoint 0 92) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨92,by decide⟩).scale 1 12) = p0_92.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨92,by decide⟩
  have he : PointBox.calc p0_92.t = p0_92 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_93_contains : p0_93.Contains (quadraturePoint 0 93) := by
  have ht : p0_93.t.Contains (quadraturePoint 0 93) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨93,by decide⟩).scale 1 12) = p0_93.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨93,by decide⟩
  have he : PointBox.calc p0_93.t = p0_93 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_94_contains : p0_94.Contains (quadraturePoint 0 94) := by
  have ht : p0_94.t.Contains (quadraturePoint 0 94) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨94,by decide⟩).scale 1 12) = p0_94.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨94,by decide⟩
  have he : PointBox.calc p0_94.t = p0_94 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_95_contains : p0_95.Contains (quadraturePoint 0 95) := by
  have ht : p0_95.t.Contains (quadraturePoint 0 95) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨95,by decide⟩).scale 1 12) = p0_95.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨95,by decide⟩
  have he : PointBox.calc p0_95.t = p0_95 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_224_contains : p0_224.Contains (quadraturePoint 0 224) := by
  have ht : p0_224.t.Contains (quadraturePoint 0 224) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨224,by decide⟩).scale 1 12) = p0_224.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨224,by decide⟩
  have he : PointBox.calc p0_224.t = p0_224 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_225_contains : p0_225.Contains (quadraturePoint 0 225) := by
  have ht : p0_225.t.Contains (quadraturePoint 0 225) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨225,by decide⟩).scale 1 12) = p0_225.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨225,by decide⟩
  have he : PointBox.calc p0_225.t = p0_225 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_226_contains : p0_226.Contains (quadraturePoint 0 226) := by
  have ht : p0_226.t.Contains (quadraturePoint 0 226) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨226,by decide⟩).scale 1 12) = p0_226.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨226,by decide⟩
  have he : PointBox.calc p0_226.t = p0_226 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_227_contains : p0_227.Contains (quadraturePoint 0 227) := by
  have ht : p0_227.t.Contains (quadraturePoint 0 227) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨227,by decide⟩).scale 1 12) = p0_227.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨227,by decide⟩
  have he : PointBox.calc p0_227.t = p0_227 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_228_contains : p0_228.Contains (quadraturePoint 0 228) := by
  have ht : p0_228.t.Contains (quadraturePoint 0 228) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨228,by decide⟩).scale 1 12) = p0_228.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨228,by decide⟩
  have he : PointBox.calc p0_228.t = p0_228 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_229_contains : p0_229.Contains (quadraturePoint 0 229) := by
  have ht : p0_229.t.Contains (quadraturePoint 0 229) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨229,by decide⟩).scale 1 12) = p0_229.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨229,by decide⟩
  have he : PointBox.calc p0_229.t = p0_229 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_230_contains : p0_230.Contains (quadraturePoint 0 230) := by
  have ht : p0_230.t.Contains (quadraturePoint 0 230) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨230,by decide⟩).scale 1 12) = p0_230.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨230,by decide⟩
  have he : PointBox.calc p0_230.t = p0_230 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_231_contains : p0_231.Contains (quadraturePoint 0 231) := by
  have ht : p0_231.t.Contains (quadraturePoint 0 231) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨231,by decide⟩).scale 1 12) = p0_231.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨231,by decide⟩
  have he : PointBox.calc p0_231.t = p0_231 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_232_contains : p0_232.Contains (quadraturePoint 0 232) := by
  have ht : p0_232.t.Contains (quadraturePoint 0 232) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨232,by decide⟩).scale 1 12) = p0_232.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨232,by decide⟩
  have he : PointBox.calc p0_232.t = p0_232 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_233_contains : p0_233.Contains (quadraturePoint 0 233) := by
  have ht : p0_233.t.Contains (quadraturePoint 0 233) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨233,by decide⟩).scale 1 12) = p0_233.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨233,by decide⟩
  have he : PointBox.calc p0_233.t = p0_233 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_234_contains : p0_234.Contains (quadraturePoint 0 234) := by
  have ht : p0_234.t.Contains (quadraturePoint 0 234) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨234,by decide⟩).scale 1 12) = p0_234.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨234,by decide⟩
  have he : PointBox.calc p0_234.t = p0_234 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_235_contains : p0_235.Contains (quadraturePoint 0 235) := by
  have ht : p0_235.t.Contains (quadraturePoint 0 235) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨235,by decide⟩).scale 1 12) = p0_235.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨235,by decide⟩
  have he : PointBox.calc p0_235.t = p0_235 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_236_contains : p0_236.Contains (quadraturePoint 0 236) := by
  have ht : p0_236.t.Contains (quadraturePoint 0 236) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨236,by decide⟩).scale 1 12) = p0_236.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨236,by decide⟩
  have he : PointBox.calc p0_236.t = p0_236 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_237_contains : p0_237.Contains (quadraturePoint 0 237) := by
  have ht : p0_237.t.Contains (quadraturePoint 0 237) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨237,by decide⟩).scale 1 12) = p0_237.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨237,by decide⟩
  have he : PointBox.calc p0_237.t = p0_237 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_238_contains : p0_238.Contains (quadraturePoint 0 238) := by
  have ht : p0_238.t.Contains (quadraturePoint 0 238) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨238,by decide⟩).scale 1 12) = p0_238.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨238,by decide⟩
  have he : PointBox.calc p0_238.t = p0_238 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_239_contains : p0_239.Contains (quadraturePoint 0 239) := by
  have ht : p0_239.t.Contains (quadraturePoint 0 239) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨239,by decide⟩).scale 1 12) = p0_239.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨239,by decide⟩
  have he : PointBox.calc p0_239.t = p0_239 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_240_contains : p0_240.Contains (quadraturePoint 0 240) := by
  have ht : p0_240.t.Contains (quadraturePoint 0 240) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨240,by decide⟩).scale 1 12) = p0_240.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨240,by decide⟩
  have he : PointBox.calc p0_240.t = p0_240 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_241_contains : p0_241.Contains (quadraturePoint 0 241) := by
  have ht : p0_241.t.Contains (quadraturePoint 0 241) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨241,by decide⟩).scale 1 12) = p0_241.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨241,by decide⟩
  have he : PointBox.calc p0_241.t = p0_241 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_242_contains : p0_242.Contains (quadraturePoint 0 242) := by
  have ht : p0_242.t.Contains (quadraturePoint 0 242) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨242,by decide⟩).scale 1 12) = p0_242.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨242,by decide⟩
  have he : PointBox.calc p0_242.t = p0_242 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_243_contains : p0_243.Contains (quadraturePoint 0 243) := by
  have ht : p0_243.t.Contains (quadraturePoint 0 243) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨243,by decide⟩).scale 1 12) = p0_243.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨243,by decide⟩
  have he : PointBox.calc p0_243.t = p0_243 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_244_contains : p0_244.Contains (quadraturePoint 0 244) := by
  have ht : p0_244.t.Contains (quadraturePoint 0 244) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨244,by decide⟩).scale 1 12) = p0_244.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨244,by decide⟩
  have he : PointBox.calc p0_244.t = p0_244 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_245_contains : p0_245.Contains (quadraturePoint 0 245) := by
  have ht : p0_245.t.Contains (quadraturePoint 0 245) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨245,by decide⟩).scale 1 12) = p0_245.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨245,by decide⟩
  have he : PointBox.calc p0_245.t = p0_245 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_246_contains : p0_246.Contains (quadraturePoint 0 246) := by
  have ht : p0_246.t.Contains (quadraturePoint 0 246) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨246,by decide⟩).scale 1 12) = p0_246.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨246,by decide⟩
  have he : PointBox.calc p0_246.t = p0_246 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_247_contains : p0_247.Contains (quadraturePoint 0 247) := by
  have ht : p0_247.t.Contains (quadraturePoint 0 247) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨247,by decide⟩).scale 1 12) = p0_247.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨247,by decide⟩
  have he : PointBox.calc p0_247.t = p0_247 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_248_contains : p0_248.Contains (quadraturePoint 0 248) := by
  have ht : p0_248.t.Contains (quadraturePoint 0 248) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨248,by decide⟩).scale 1 12) = p0_248.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨248,by decide⟩
  have he : PointBox.calc p0_248.t = p0_248 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_249_contains : p0_249.Contains (quadraturePoint 0 249) := by
  have ht : p0_249.t.Contains (quadraturePoint 0 249) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨249,by decide⟩).scale 1 12) = p0_249.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨249,by decide⟩
  have he : PointBox.calc p0_249.t = p0_249 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_250_contains : p0_250.Contains (quadraturePoint 0 250) := by
  have ht : p0_250.t.Contains (quadraturePoint 0 250) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨250,by decide⟩).scale 1 12) = p0_250.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨250,by decide⟩
  have he : PointBox.calc p0_250.t = p0_250 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_251_contains : p0_251.Contains (quadraturePoint 0 251) := by
  have ht : p0_251.t.Contains (quadraturePoint 0 251) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨251,by decide⟩).scale 1 12) = p0_251.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨251,by decide⟩
  have he : PointBox.calc p0_251.t = p0_251 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_252_contains : p0_252.Contains (quadraturePoint 0 252) := by
  have ht : p0_252.t.Contains (quadraturePoint 0 252) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨252,by decide⟩).scale 1 12) = p0_252.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨252,by decide⟩
  have he : PointBox.calc p0_252.t = p0_252 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_253_contains : p0_253.Contains (quadraturePoint 0 253) := by
  have ht : p0_253.t.Contains (quadraturePoint 0 253) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨253,by decide⟩).scale 1 12) = p0_253.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨253,by decide⟩
  have he : PointBox.calc p0_253.t = p0_253 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_254_contains : p0_254.Contains (quadraturePoint 0 254) := by
  have ht : p0_254.t.Contains (quadraturePoint 0 254) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨254,by decide⟩).scale 1 12) = p0_254.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨254,by decide⟩
  have he : PointBox.calc p0_254.t = p0_254 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_255_contains : p0_255.Contains (quadraturePoint 0 255) := by
  have ht : p0_255.t.Contains (quadraturePoint 0 255) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨255,by decide⟩).scale 1 12) = p0_255.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨255,by decide⟩
  have he : PointBox.calc p0_255.t = p0_255 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_0_contains (k : Fin 16) : (row0_0 k).Contains (quadraturePoint 0 (0+k.val)) := by
  fin_cases k
  · exact p0_0_contains
  · exact p0_1_contains
  · exact p0_2_contains
  · exact p0_3_contains
  · exact p0_4_contains
  · exact p0_5_contains
  · exact p0_6_contains
  · exact p0_7_contains
  · exact p0_8_contains
  · exact p0_9_contains
  · exact p0_10_contains
  · exact p0_11_contains
  · exact p0_12_contains
  · exact p0_13_contains
  · exact p0_14_contains
  · exact p0_15_contains
lemma row0_5_contains (k : Fin 16) : (row0_5 k).Contains (quadraturePoint 0 (80+k.val)) := by
  fin_cases k
  · exact p0_80_contains
  · exact p0_81_contains
  · exact p0_82_contains
  · exact p0_83_contains
  · exact p0_84_contains
  · exact p0_85_contains
  · exact p0_86_contains
  · exact p0_87_contains
  · exact p0_88_contains
  · exact p0_89_contains
  · exact p0_90_contains
  · exact p0_91_contains
  · exact p0_92_contains
  · exact p0_93_contains
  · exact p0_94_contains
  · exact p0_95_contains
lemma row0_14_contains (k : Fin 16) : (row0_14 k).Contains (quadraturePoint 0 (224+k.val)) := by
  fin_cases k
  · exact p0_224_contains
  · exact p0_225_contains
  · exact p0_226_contains
  · exact p0_227_contains
  · exact p0_228_contains
  · exact p0_229_contains
  · exact p0_230_contains
  · exact p0_231_contains
  · exact p0_232_contains
  · exact p0_233_contains
  · exact p0_234_contains
  · exact p0_235_contains
  · exact p0_236_contains
  · exact p0_237_contains
  · exact p0_238_contains
  · exact p0_239_contains
lemma row0_15_contains (k : Fin 16) : (row0_15 k).Contains (quadraturePoint 0 (240+k.val)) := by
  fin_cases k
  · exact p0_240_contains
  · exact p0_241_contains
  · exact p0_242_contains
  · exact p0_243_contains
  · exact p0_244_contains
  · exact p0_245_contains
  · exact p0_246_contains
  · exact p0_247_contains
  · exact p0_248_contains
  · exact p0_249_contains
  · exact p0_250_contains
  · exact p0_251_contains
  · exact p0_252_contains
  · exact p0_253_contains
  · exact p0_254_contains
  · exact p0_255_contains
lemma row0_contains (i k : Fin 16) : (row0 i k).Contains (quadraturePoint 0 (16*i.val+k.val)) := by
  fin_cases i
  · exact row0_0_contains k
  · exact row0_1_contains_g k
  · exact row0_2_contains_g k
  · exact row0_3_contains_g k
  · exact row0_4_contains_g k
  · exact row0_5_contains k
  · exact row0_6_contains_g k
  · exact row0_7_contains_g k
  · exact row0_8_contains_g k
  · exact row0_9_contains_g k
  · exact row0_10_contains_g k
  · exact row0_11_contains_g k
  · exact row0_12_contains_g k
  · exact row0_13_contains_g k
  · exact row0_14_contains k
  · exact row0_15_contains k
lemma gridRows_contains_g_oai (j : Fin 6) (i k : Fin 16) : (gridRows j i k).Contains (quadraturePoint j.val (16*i.val+k.val)) := by
  fin_cases j
  · exact row0_contains i k
  · exact row1_contains_g i k
  · exact row2_contains_g i k
  · exact row3_contains_g i k
  · exact row4_contains_g i k
  · exact row5_contains_g i k
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.gridRows_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.gridRows_contains_g_oai
