-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row1_6_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:22.730212+00:00
-- url     : https://prove2.me/submissions/5e07ee28-01d2-4cf4-ba50-018dfadea5b7

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

lemma p1_96_contains : p1_96.Contains (quadraturePoint 1 96) := by
  have ht : p1_96.t.Contains (quadraturePoint 1 96) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨96,by decide⟩).scale 1 12) = p1_96.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨96,by decide⟩
  have he : PointBox.calc p1_96.t = p1_96 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_97_contains : p1_97.Contains (quadraturePoint 1 97) := by
  have ht : p1_97.t.Contains (quadraturePoint 1 97) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p1_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨97,by decide⟩
  have he : PointBox.calc p1_97.t = p1_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_98_contains : p1_98.Contains (quadraturePoint 1 98) := by
  have ht : p1_98.t.Contains (quadraturePoint 1 98) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨98,by decide⟩).scale 1 12) = p1_98.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨98,by decide⟩
  have he : PointBox.calc p1_98.t = p1_98 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_99_contains : p1_99.Contains (quadraturePoint 1 99) := by
  have ht : p1_99.t.Contains (quadraturePoint 1 99) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨99,by decide⟩).scale 1 12) = p1_99.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨99,by decide⟩
  have he : PointBox.calc p1_99.t = p1_99 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_100_contains : p1_100.Contains (quadraturePoint 1 100) := by
  have ht : p1_100.t.Contains (quadraturePoint 1 100) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨100,by decide⟩).scale 1 12) = p1_100.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨100,by decide⟩
  have he : PointBox.calc p1_100.t = p1_100 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_101_contains : p1_101.Contains (quadraturePoint 1 101) := by
  have ht : p1_101.t.Contains (quadraturePoint 1 101) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨101,by decide⟩).scale 1 12) = p1_101.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨101,by decide⟩
  have he : PointBox.calc p1_101.t = p1_101 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_102_contains : p1_102.Contains (quadraturePoint 1 102) := by
  have ht : p1_102.t.Contains (quadraturePoint 1 102) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨102,by decide⟩).scale 1 12) = p1_102.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨102,by decide⟩
  have he : PointBox.calc p1_102.t = p1_102 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_103_contains : p1_103.Contains (quadraturePoint 1 103) := by
  have ht : p1_103.t.Contains (quadraturePoint 1 103) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨103,by decide⟩).scale 1 12) = p1_103.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨103,by decide⟩
  have he : PointBox.calc p1_103.t = p1_103 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_104_contains : p1_104.Contains (quadraturePoint 1 104) := by
  have ht : p1_104.t.Contains (quadraturePoint 1 104) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨104,by decide⟩).scale 1 12) = p1_104.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨104,by decide⟩
  have he : PointBox.calc p1_104.t = p1_104 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_105_contains : p1_105.Contains (quadraturePoint 1 105) := by
  have ht : p1_105.t.Contains (quadraturePoint 1 105) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨105,by decide⟩).scale 1 12) = p1_105.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨105,by decide⟩
  have he : PointBox.calc p1_105.t = p1_105 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_106_contains : p1_106.Contains (quadraturePoint 1 106) := by
  have ht : p1_106.t.Contains (quadraturePoint 1 106) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨106,by decide⟩).scale 1 12) = p1_106.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨106,by decide⟩
  have he : PointBox.calc p1_106.t = p1_106 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_107_contains : p1_107.Contains (quadraturePoint 1 107) := by
  have ht : p1_107.t.Contains (quadraturePoint 1 107) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨107,by decide⟩).scale 1 12) = p1_107.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨107,by decide⟩
  have he : PointBox.calc p1_107.t = p1_107 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_108_contains : p1_108.Contains (quadraturePoint 1 108) := by
  have ht : p1_108.t.Contains (quadraturePoint 1 108) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨108,by decide⟩).scale 1 12) = p1_108.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨108,by decide⟩
  have he : PointBox.calc p1_108.t = p1_108 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_109_contains : p1_109.Contains (quadraturePoint 1 109) := by
  have ht : p1_109.t.Contains (quadraturePoint 1 109) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨109,by decide⟩).scale 1 12) = p1_109.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨109,by decide⟩
  have he : PointBox.calc p1_109.t = p1_109 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_110_contains : p1_110.Contains (quadraturePoint 1 110) := by
  have ht : p1_110.t.Contains (quadraturePoint 1 110) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨110,by decide⟩).scale 1 12) = p1_110.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨110,by decide⟩
  have he : PointBox.calc p1_110.t = p1_110 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p1_111_contains : p1_111.Contains (quadraturePoint 1 111) := by
  have ht : p1_111.t.Contains (quadraturePoint 1 111) := by
    have he : (RBox.rat 3 12).add ((nodeLookup ⟨111,by decide⟩).scale 1 12) = p1_111.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 1 ⟨111,by decide⟩
  have he : PointBox.calc p1_111.t = p1_111 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row1_6_contains_g_oai (k : Fin 16) : (row1_6 k).Contains (quadraturePoint 1 (96+k.val)) := by
  fin_cases k
  · exact p1_96_contains
  · exact p1_97_contains
  · exact p1_98_contains
  · exact p1_99_contains
  · exact p1_100_contains
  · exact p1_101_contains
  · exact p1_102_contains
  · exact p1_103_contains
  · exact p1_104_contains
  · exact p1_105_contains
  · exact p1_106_contains
  · exact p1_107_contains
  · exact p1_108_contains
  · exact p1_109_contains
  · exact p1_110_contains
  · exact p1_111_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row1_6_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row1_6_contains_g_oai
