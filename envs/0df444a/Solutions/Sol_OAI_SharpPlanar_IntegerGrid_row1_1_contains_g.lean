-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:19.555562+00:00
-- url     : https://prove2.me/submissions/2be7656d-b657-49bb-bc19-89074d9bc8b5

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

lemma p1_16_contains : p1_16.Contains (quadraturePoint 1 16) := by
  have ht : p1_16.t.Contains (quadraturePoint 1 16) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p1_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨16,by decide⟩
  have he : PointBox.calc p1_16.t = p1_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_17_contains : p1_17.Contains (quadraturePoint 1 17) := by
  have ht : p1_17.t.Contains (quadraturePoint 1 17) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p1_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨17,by decide⟩
  have he : PointBox.calc p1_17.t = p1_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_18_contains : p1_18.Contains (quadraturePoint 1 18) := by
  have ht : p1_18.t.Contains (quadraturePoint 1 18) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p1_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨18,by decide⟩
  have he : PointBox.calc p1_18.t = p1_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_19_contains : p1_19.Contains (quadraturePoint 1 19) := by
  have ht : p1_19.t.Contains (quadraturePoint 1 19) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p1_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨19,by decide⟩
  have he : PointBox.calc p1_19.t = p1_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_20_contains : p1_20.Contains (quadraturePoint 1 20) := by
  have ht : p1_20.t.Contains (quadraturePoint 1 20) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p1_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨20,by decide⟩
  have he : PointBox.calc p1_20.t = p1_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_21_contains : p1_21.Contains (quadraturePoint 1 21) := by
  have ht : p1_21.t.Contains (quadraturePoint 1 21) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p1_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨21,by decide⟩
  have he : PointBox.calc p1_21.t = p1_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_22_contains : p1_22.Contains (quadraturePoint 1 22) := by
  have ht : p1_22.t.Contains (quadraturePoint 1 22) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p1_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨22,by decide⟩
  have he : PointBox.calc p1_22.t = p1_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_23_contains : p1_23.Contains (quadraturePoint 1 23) := by
  have ht : p1_23.t.Contains (quadraturePoint 1 23) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p1_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨23,by decide⟩
  have he : PointBox.calc p1_23.t = p1_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_24_contains : p1_24.Contains (quadraturePoint 1 24) := by
  have ht : p1_24.t.Contains (quadraturePoint 1 24) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p1_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨24,by decide⟩
  have he : PointBox.calc p1_24.t = p1_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_25_contains : p1_25.Contains (quadraturePoint 1 25) := by
  have ht : p1_25.t.Contains (quadraturePoint 1 25) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p1_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨25,by decide⟩
  have he : PointBox.calc p1_25.t = p1_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_26_contains : p1_26.Contains (quadraturePoint 1 26) := by
  have ht : p1_26.t.Contains (quadraturePoint 1 26) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p1_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨26,by decide⟩
  have he : PointBox.calc p1_26.t = p1_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_27_contains : p1_27.Contains (quadraturePoint 1 27) := by
  have ht : p1_27.t.Contains (quadraturePoint 1 27) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p1_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨27,by decide⟩
  have he : PointBox.calc p1_27.t = p1_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_28_contains : p1_28.Contains (quadraturePoint 1 28) := by
  have ht : p1_28.t.Contains (quadraturePoint 1 28) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p1_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨28,by decide⟩
  have he : PointBox.calc p1_28.t = p1_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_29_contains : p1_29.Contains (quadraturePoint 1 29) := by
  have ht : p1_29.t.Contains (quadraturePoint 1 29) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p1_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨29,by decide⟩
  have he : PointBox.calc p1_29.t = p1_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_30_contains : p1_30.Contains (quadraturePoint 1 30) := by
  have ht : p1_30.t.Contains (quadraturePoint 1 30) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p1_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨30,by decide⟩
  have he : PointBox.calc p1_30.t = p1_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_31_contains : p1_31.Contains (quadraturePoint 1 31) := by
  have ht : p1_31.t.Contains (quadraturePoint 1 31) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p1_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨31,by decide⟩
  have he : PointBox.calc p1_31.t = p1_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_1_contains_g_oai (k : Fin 16) : (row1_1 k).Contains (quadraturePoint 1 (16+k.val)) := by
  fin_cases k
  · exact p1_16_contains
  · exact p1_17_contains
  · exact p1_18_contains
  · exact p1_19_contains
  · exact p1_20_contains
  · exact p1_21_contains
  · exact p1_22_contains
  · exact p1_23_contains
  · exact p1_24_contains
  · exact p1_25_contains
  · exact p1_26_contains
  · exact p1_27_contains
  · exact p1_28_contains
  · exact p1_29_contains
  · exact p1_30_contains
  · exact p1_31_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_1_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_1_contains_g_oai
