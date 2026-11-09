-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:31.921352+00:00
-- url     : https://prove2.me/submissions/b1a88e00-2994-41e4-9f56-19d0743b3ea5

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

lemma p0_64_contains : p0_64.Contains (quadraturePoint 0 64) := by
  have ht : p0_64.t.Contains (quadraturePoint 0 64) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨64,by decide⟩).scale 1 12) = p0_64.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨64,by decide⟩
  have he : PointBox.calc p0_64.t = p0_64 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_65_contains : p0_65.Contains (quadraturePoint 0 65) := by
  have ht : p0_65.t.Contains (quadraturePoint 0 65) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨65,by decide⟩).scale 1 12) = p0_65.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨65,by decide⟩
  have he : PointBox.calc p0_65.t = p0_65 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_66_contains : p0_66.Contains (quadraturePoint 0 66) := by
  have ht : p0_66.t.Contains (quadraturePoint 0 66) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨66,by decide⟩).scale 1 12) = p0_66.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨66,by decide⟩
  have he : PointBox.calc p0_66.t = p0_66 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_67_contains : p0_67.Contains (quadraturePoint 0 67) := by
  have ht : p0_67.t.Contains (quadraturePoint 0 67) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨67,by decide⟩).scale 1 12) = p0_67.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨67,by decide⟩
  have he : PointBox.calc p0_67.t = p0_67 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_68_contains : p0_68.Contains (quadraturePoint 0 68) := by
  have ht : p0_68.t.Contains (quadraturePoint 0 68) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨68,by decide⟩).scale 1 12) = p0_68.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨68,by decide⟩
  have he : PointBox.calc p0_68.t = p0_68 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_69_contains : p0_69.Contains (quadraturePoint 0 69) := by
  have ht : p0_69.t.Contains (quadraturePoint 0 69) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨69,by decide⟩).scale 1 12) = p0_69.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨69,by decide⟩
  have he : PointBox.calc p0_69.t = p0_69 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_70_contains : p0_70.Contains (quadraturePoint 0 70) := by
  have ht : p0_70.t.Contains (quadraturePoint 0 70) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨70,by decide⟩).scale 1 12) = p0_70.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨70,by decide⟩
  have he : PointBox.calc p0_70.t = p0_70 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_71_contains : p0_71.Contains (quadraturePoint 0 71) := by
  have ht : p0_71.t.Contains (quadraturePoint 0 71) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨71,by decide⟩).scale 1 12) = p0_71.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨71,by decide⟩
  have he : PointBox.calc p0_71.t = p0_71 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_72_contains : p0_72.Contains (quadraturePoint 0 72) := by
  have ht : p0_72.t.Contains (quadraturePoint 0 72) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨72,by decide⟩).scale 1 12) = p0_72.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨72,by decide⟩
  have he : PointBox.calc p0_72.t = p0_72 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_73_contains : p0_73.Contains (quadraturePoint 0 73) := by
  have ht : p0_73.t.Contains (quadraturePoint 0 73) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨73,by decide⟩).scale 1 12) = p0_73.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨73,by decide⟩
  have he : PointBox.calc p0_73.t = p0_73 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_74_contains : p0_74.Contains (quadraturePoint 0 74) := by
  have ht : p0_74.t.Contains (quadraturePoint 0 74) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨74,by decide⟩).scale 1 12) = p0_74.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨74,by decide⟩
  have he : PointBox.calc p0_74.t = p0_74 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_75_contains : p0_75.Contains (quadraturePoint 0 75) := by
  have ht : p0_75.t.Contains (quadraturePoint 0 75) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨75,by decide⟩).scale 1 12) = p0_75.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨75,by decide⟩
  have he : PointBox.calc p0_75.t = p0_75 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_76_contains : p0_76.Contains (quadraturePoint 0 76) := by
  have ht : p0_76.t.Contains (quadraturePoint 0 76) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p0_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨76,by decide⟩
  have he : PointBox.calc p0_76.t = p0_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_77_contains : p0_77.Contains (quadraturePoint 0 77) := by
  have ht : p0_77.t.Contains (quadraturePoint 0 77) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨77,by decide⟩).scale 1 12) = p0_77.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨77,by decide⟩
  have he : PointBox.calc p0_77.t = p0_77 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_78_contains : p0_78.Contains (quadraturePoint 0 78) := by
  have ht : p0_78.t.Contains (quadraturePoint 0 78) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨78,by decide⟩).scale 1 12) = p0_78.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨78,by decide⟩
  have he : PointBox.calc p0_78.t = p0_78 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_79_contains : p0_79.Contains (quadraturePoint 0 79) := by
  have ht : p0_79.t.Contains (quadraturePoint 0 79) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨79,by decide⟩).scale 1 12) = p0_79.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨79,by decide⟩
  have he : PointBox.calc p0_79.t = p0_79 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_4_contains_g_oai (k : Fin 16) : (row0_4 k).Contains (quadraturePoint 0 (64+k.val)) := by
  fin_cases k
  · exact p0_64_contains
  · exact p0_65_contains
  · exact p0_66_contains
  · exact p0_67_contains
  · exact p0_68_contains
  · exact p0_69_contains
  · exact p0_70_contains
  · exact p0_71_contains
  · exact p0_72_contains
  · exact p0_73_contains
  · exact p0_74_contains
  · exact p0_75_contains
  · exact p0_76_contains
  · exact p0_77_contains
  · exact p0_78_contains
  · exact p0_79_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_4_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_4_contains_g_oai
