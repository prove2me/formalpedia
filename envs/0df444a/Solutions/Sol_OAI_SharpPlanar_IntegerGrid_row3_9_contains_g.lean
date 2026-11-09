-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row3_9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:49.129455+00:00
-- url     : https://prove2.me/submissions/f82a70ed-9217-421d-88bd-8679e595e6f7

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

lemma p3_144_contains : p3_144.Contains (quadraturePoint 3 144) := by
  have ht : p3_144.t.Contains (quadraturePoint 3 144) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨144,by decide⟩).scale 1 12) = p3_144.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨144,by decide⟩
  have he : PointBox.calc p3_144.t = p3_144 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_145_contains : p3_145.Contains (quadraturePoint 3 145) := by
  have ht : p3_145.t.Contains (quadraturePoint 3 145) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨145,by decide⟩).scale 1 12) = p3_145.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨145,by decide⟩
  have he : PointBox.calc p3_145.t = p3_145 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_146_contains : p3_146.Contains (quadraturePoint 3 146) := by
  have ht : p3_146.t.Contains (quadraturePoint 3 146) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨146,by decide⟩).scale 1 12) = p3_146.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨146,by decide⟩
  have he : PointBox.calc p3_146.t = p3_146 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_147_contains : p3_147.Contains (quadraturePoint 3 147) := by
  have ht : p3_147.t.Contains (quadraturePoint 3 147) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨147,by decide⟩).scale 1 12) = p3_147.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨147,by decide⟩
  have he : PointBox.calc p3_147.t = p3_147 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_148_contains : p3_148.Contains (quadraturePoint 3 148) := by
  have ht : p3_148.t.Contains (quadraturePoint 3 148) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨148,by decide⟩).scale 1 12) = p3_148.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨148,by decide⟩
  have he : PointBox.calc p3_148.t = p3_148 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_149_contains : p3_149.Contains (quadraturePoint 3 149) := by
  have ht : p3_149.t.Contains (quadraturePoint 3 149) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨149,by decide⟩).scale 1 12) = p3_149.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨149,by decide⟩
  have he : PointBox.calc p3_149.t = p3_149 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_150_contains : p3_150.Contains (quadraturePoint 3 150) := by
  have ht : p3_150.t.Contains (quadraturePoint 3 150) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨150,by decide⟩).scale 1 12) = p3_150.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨150,by decide⟩
  have he : PointBox.calc p3_150.t = p3_150 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_151_contains : p3_151.Contains (quadraturePoint 3 151) := by
  have ht : p3_151.t.Contains (quadraturePoint 3 151) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨151,by decide⟩).scale 1 12) = p3_151.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨151,by decide⟩
  have he : PointBox.calc p3_151.t = p3_151 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_152_contains : p3_152.Contains (quadraturePoint 3 152) := by
  have ht : p3_152.t.Contains (quadraturePoint 3 152) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨152,by decide⟩).scale 1 12) = p3_152.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨152,by decide⟩
  have he : PointBox.calc p3_152.t = p3_152 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_153_contains : p3_153.Contains (quadraturePoint 3 153) := by
  have ht : p3_153.t.Contains (quadraturePoint 3 153) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨153,by decide⟩).scale 1 12) = p3_153.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨153,by decide⟩
  have he : PointBox.calc p3_153.t = p3_153 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_154_contains : p3_154.Contains (quadraturePoint 3 154) := by
  have ht : p3_154.t.Contains (quadraturePoint 3 154) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨154,by decide⟩).scale 1 12) = p3_154.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨154,by decide⟩
  have he : PointBox.calc p3_154.t = p3_154 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_155_contains : p3_155.Contains (quadraturePoint 3 155) := by
  have ht : p3_155.t.Contains (quadraturePoint 3 155) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨155,by decide⟩).scale 1 12) = p3_155.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨155,by decide⟩
  have he : PointBox.calc p3_155.t = p3_155 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_156_contains : p3_156.Contains (quadraturePoint 3 156) := by
  have ht : p3_156.t.Contains (quadraturePoint 3 156) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨156,by decide⟩).scale 1 12) = p3_156.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨156,by decide⟩
  have he : PointBox.calc p3_156.t = p3_156 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_157_contains : p3_157.Contains (quadraturePoint 3 157) := by
  have ht : p3_157.t.Contains (quadraturePoint 3 157) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨157,by decide⟩).scale 1 12) = p3_157.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨157,by decide⟩
  have he : PointBox.calc p3_157.t = p3_157 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_158_contains : p3_158.Contains (quadraturePoint 3 158) := by
  have ht : p3_158.t.Contains (quadraturePoint 3 158) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨158,by decide⟩).scale 1 12) = p3_158.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨158,by decide⟩
  have he : PointBox.calc p3_158.t = p3_158 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p3_159_contains : p3_159.Contains (quadraturePoint 3 159) := by
  have ht : p3_159.t.Contains (quadraturePoint 3 159) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨159,by decide⟩).scale 1 12) = p3_159.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨159,by decide⟩
  have he : PointBox.calc p3_159.t = p3_159 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row3_9_contains_g_oai (k : Fin 16) : (row3_9 k).Contains (quadraturePoint 3 (144+k.val)) := by
  fin_cases k
  · exact p3_144_contains
  · exact p3_145_contains
  · exact p3_146_contains
  · exact p3_147_contains
  · exact p3_148_contains
  · exact p3_149_contains
  · exact p3_150_contains
  · exact p3_151_contains
  · exact p3_152_contains
  · exact p3_153_contains
  · exact p3_154_contains
  · exact p3_155_contains
  · exact p3_156_contains
  · exact p3_157_contains
  · exact p3_158_contains
  · exact p3_159_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row3_9_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row3_9_contains_g_oai
