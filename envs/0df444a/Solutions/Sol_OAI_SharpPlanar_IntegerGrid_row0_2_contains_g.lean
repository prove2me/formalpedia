-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:01.692897+00:00
-- url     : https://prove2.me/submissions/fcc0b652-0089-41f9-afaa-6de019cc06ce

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

lemma p0_32_contains : p0_32.Contains (quadraturePoint 0 32) := by
  have ht : p0_32.t.Contains (quadraturePoint 0 32) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨32,by decide⟩).scale 1 12) = p0_32.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨32,by decide⟩
  have he : PointBox.calc p0_32.t = p0_32 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_33_contains : p0_33.Contains (quadraturePoint 0 33) := by
  have ht : p0_33.t.Contains (quadraturePoint 0 33) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨33,by decide⟩).scale 1 12) = p0_33.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨33,by decide⟩
  have he : PointBox.calc p0_33.t = p0_33 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_34_contains : p0_34.Contains (quadraturePoint 0 34) := by
  have ht : p0_34.t.Contains (quadraturePoint 0 34) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨34,by decide⟩).scale 1 12) = p0_34.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨34,by decide⟩
  have he : PointBox.calc p0_34.t = p0_34 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_35_contains : p0_35.Contains (quadraturePoint 0 35) := by
  have ht : p0_35.t.Contains (quadraturePoint 0 35) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨35,by decide⟩).scale 1 12) = p0_35.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨35,by decide⟩
  have he : PointBox.calc p0_35.t = p0_35 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_36_contains : p0_36.Contains (quadraturePoint 0 36) := by
  have ht : p0_36.t.Contains (quadraturePoint 0 36) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨36,by decide⟩).scale 1 12) = p0_36.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨36,by decide⟩
  have he : PointBox.calc p0_36.t = p0_36 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_37_contains : p0_37.Contains (quadraturePoint 0 37) := by
  have ht : p0_37.t.Contains (quadraturePoint 0 37) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨37,by decide⟩).scale 1 12) = p0_37.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨37,by decide⟩
  have he : PointBox.calc p0_37.t = p0_37 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_38_contains : p0_38.Contains (quadraturePoint 0 38) := by
  have ht : p0_38.t.Contains (quadraturePoint 0 38) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨38,by decide⟩).scale 1 12) = p0_38.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨38,by decide⟩
  have he : PointBox.calc p0_38.t = p0_38 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_39_contains : p0_39.Contains (quadraturePoint 0 39) := by
  have ht : p0_39.t.Contains (quadraturePoint 0 39) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨39,by decide⟩).scale 1 12) = p0_39.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨39,by decide⟩
  have he : PointBox.calc p0_39.t = p0_39 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_40_contains : p0_40.Contains (quadraturePoint 0 40) := by
  have ht : p0_40.t.Contains (quadraturePoint 0 40) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨40,by decide⟩).scale 1 12) = p0_40.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨40,by decide⟩
  have he : PointBox.calc p0_40.t = p0_40 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_41_contains : p0_41.Contains (quadraturePoint 0 41) := by
  have ht : p0_41.t.Contains (quadraturePoint 0 41) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨41,by decide⟩).scale 1 12) = p0_41.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨41,by decide⟩
  have he : PointBox.calc p0_41.t = p0_41 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_42_contains : p0_42.Contains (quadraturePoint 0 42) := by
  have ht : p0_42.t.Contains (quadraturePoint 0 42) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨42,by decide⟩).scale 1 12) = p0_42.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨42,by decide⟩
  have he : PointBox.calc p0_42.t = p0_42 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_43_contains : p0_43.Contains (quadraturePoint 0 43) := by
  have ht : p0_43.t.Contains (quadraturePoint 0 43) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨43,by decide⟩).scale 1 12) = p0_43.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨43,by decide⟩
  have he : PointBox.calc p0_43.t = p0_43 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_44_contains : p0_44.Contains (quadraturePoint 0 44) := by
  have ht : p0_44.t.Contains (quadraturePoint 0 44) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨44,by decide⟩).scale 1 12) = p0_44.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨44,by decide⟩
  have he : PointBox.calc p0_44.t = p0_44 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_45_contains : p0_45.Contains (quadraturePoint 0 45) := by
  have ht : p0_45.t.Contains (quadraturePoint 0 45) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨45,by decide⟩).scale 1 12) = p0_45.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨45,by decide⟩
  have he : PointBox.calc p0_45.t = p0_45 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_46_contains : p0_46.Contains (quadraturePoint 0 46) := by
  have ht : p0_46.t.Contains (quadraturePoint 0 46) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨46,by decide⟩).scale 1 12) = p0_46.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨46,by decide⟩
  have he : PointBox.calc p0_46.t = p0_46 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_47_contains : p0_47.Contains (quadraturePoint 0 47) := by
  have ht : p0_47.t.Contains (quadraturePoint 0 47) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨47,by decide⟩).scale 1 12) = p0_47.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨47,by decide⟩
  have he : PointBox.calc p0_47.t = p0_47 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_2_contains_g_oai (k : Fin 16) : (row0_2 k).Contains (quadraturePoint 0 (32+k.val)) := by
  fin_cases k
  · exact p0_32_contains
  · exact p0_33_contains
  · exact p0_34_contains
  · exact p0_35_contains
  · exact p0_36_contains
  · exact p0_37_contains
  · exact p0_38_contains
  · exact p0_39_contains
  · exact p0_40_contains
  · exact p0_41_contains
  · exact p0_42_contains
  · exact p0_43_contains
  · exact p0_44_contains
  · exact p0_45_contains
  · exact p0_46_contains
  · exact p0_47_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_2_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_2_contains_g_oai
