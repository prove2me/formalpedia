-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:00.350384+00:00
-- url     : https://prove2.me/submissions/14c8f9be-0a8a-4f39-9fee-6e306d0732bb

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

lemma p0_16_contains : p0_16.Contains (quadraturePoint 0 16) := by
  have ht : p0_16.t.Contains (quadraturePoint 0 16) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨16,by decide⟩).scale 1 12) = p0_16.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨16,by decide⟩
  have he : PointBox.calc p0_16.t = p0_16 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_17_contains : p0_17.Contains (quadraturePoint 0 17) := by
  have ht : p0_17.t.Contains (quadraturePoint 0 17) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨17,by decide⟩).scale 1 12) = p0_17.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨17,by decide⟩
  have he : PointBox.calc p0_17.t = p0_17 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_18_contains : p0_18.Contains (quadraturePoint 0 18) := by
  have ht : p0_18.t.Contains (quadraturePoint 0 18) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨18,by decide⟩).scale 1 12) = p0_18.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨18,by decide⟩
  have he : PointBox.calc p0_18.t = p0_18 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_19_contains : p0_19.Contains (quadraturePoint 0 19) := by
  have ht : p0_19.t.Contains (quadraturePoint 0 19) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨19,by decide⟩).scale 1 12) = p0_19.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨19,by decide⟩
  have he : PointBox.calc p0_19.t = p0_19 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_20_contains : p0_20.Contains (quadraturePoint 0 20) := by
  have ht : p0_20.t.Contains (quadraturePoint 0 20) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨20,by decide⟩).scale 1 12) = p0_20.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨20,by decide⟩
  have he : PointBox.calc p0_20.t = p0_20 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_21_contains : p0_21.Contains (quadraturePoint 0 21) := by
  have ht : p0_21.t.Contains (quadraturePoint 0 21) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨21,by decide⟩).scale 1 12) = p0_21.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨21,by decide⟩
  have he : PointBox.calc p0_21.t = p0_21 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_22_contains : p0_22.Contains (quadraturePoint 0 22) := by
  have ht : p0_22.t.Contains (quadraturePoint 0 22) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨22,by decide⟩).scale 1 12) = p0_22.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨22,by decide⟩
  have he : PointBox.calc p0_22.t = p0_22 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_23_contains : p0_23.Contains (quadraturePoint 0 23) := by
  have ht : p0_23.t.Contains (quadraturePoint 0 23) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨23,by decide⟩).scale 1 12) = p0_23.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨23,by decide⟩
  have he : PointBox.calc p0_23.t = p0_23 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_24_contains : p0_24.Contains (quadraturePoint 0 24) := by
  have ht : p0_24.t.Contains (quadraturePoint 0 24) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨24,by decide⟩).scale 1 12) = p0_24.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨24,by decide⟩
  have he : PointBox.calc p0_24.t = p0_24 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_25_contains : p0_25.Contains (quadraturePoint 0 25) := by
  have ht : p0_25.t.Contains (quadraturePoint 0 25) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨25,by decide⟩).scale 1 12) = p0_25.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨25,by decide⟩
  have he : PointBox.calc p0_25.t = p0_25 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_26_contains : p0_26.Contains (quadraturePoint 0 26) := by
  have ht : p0_26.t.Contains (quadraturePoint 0 26) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨26,by decide⟩).scale 1 12) = p0_26.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨26,by decide⟩
  have he : PointBox.calc p0_26.t = p0_26 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_27_contains : p0_27.Contains (quadraturePoint 0 27) := by
  have ht : p0_27.t.Contains (quadraturePoint 0 27) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨27,by decide⟩).scale 1 12) = p0_27.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨27,by decide⟩
  have he : PointBox.calc p0_27.t = p0_27 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_28_contains : p0_28.Contains (quadraturePoint 0 28) := by
  have ht : p0_28.t.Contains (quadraturePoint 0 28) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨28,by decide⟩).scale 1 12) = p0_28.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨28,by decide⟩
  have he : PointBox.calc p0_28.t = p0_28 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_29_contains : p0_29.Contains (quadraturePoint 0 29) := by
  have ht : p0_29.t.Contains (quadraturePoint 0 29) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨29,by decide⟩).scale 1 12) = p0_29.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨29,by decide⟩
  have he : PointBox.calc p0_29.t = p0_29 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_30_contains : p0_30.Contains (quadraturePoint 0 30) := by
  have ht : p0_30.t.Contains (quadraturePoint 0 30) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨30,by decide⟩).scale 1 12) = p0_30.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨30,by decide⟩
  have he : PointBox.calc p0_30.t = p0_30 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_31_contains : p0_31.Contains (quadraturePoint 0 31) := by
  have ht : p0_31.t.Contains (quadraturePoint 0 31) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨31,by decide⟩).scale 1 12) = p0_31.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨31,by decide⟩
  have he : PointBox.calc p0_31.t = p0_31 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_1_contains_g_oai (k : Fin 16) : (row0_1 k).Contains (quadraturePoint 0 (16+k.val)) := by
  fin_cases k
  · exact p0_16_contains
  · exact p0_17_contains
  · exact p0_18_contains
  · exact p0_19_contains
  · exact p0_20_contains
  · exact p0_21_contains
  · exact p0_22_contains
  · exact p0_23_contains
  · exact p0_24_contains
  · exact p0_25_contains
  · exact p0_26_contains
  · exact p0_27_contains
  · exact p0_28_contains
  · exact p0_29_contains
  · exact p0_30_contains
  · exact p0_31_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_1_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_1_contains_g_oai
