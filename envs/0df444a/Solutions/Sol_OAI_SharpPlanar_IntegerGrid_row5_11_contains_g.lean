-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row5_11_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:07.975304+00:00
-- url     : https://prove2.me/submissions/d44812f2-f792-440c-bb93-47ea247a86ea

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

lemma p5_176_contains : p5_176.Contains (quadraturePoint 5 176) := by
  have ht : p5_176.t.Contains (quadraturePoint 5 176) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨176,by decide⟩).scale 1 12) = p5_176.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨176,by decide⟩
  have he : PointBox.calc p5_176.t = p5_176 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_177_contains : p5_177.Contains (quadraturePoint 5 177) := by
  have ht : p5_177.t.Contains (quadraturePoint 5 177) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨177,by decide⟩).scale 1 12) = p5_177.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨177,by decide⟩
  have he : PointBox.calc p5_177.t = p5_177 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_178_contains : p5_178.Contains (quadraturePoint 5 178) := by
  have ht : p5_178.t.Contains (quadraturePoint 5 178) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨178,by decide⟩).scale 1 12) = p5_178.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨178,by decide⟩
  have he : PointBox.calc p5_178.t = p5_178 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_179_contains : p5_179.Contains (quadraturePoint 5 179) := by
  have ht : p5_179.t.Contains (quadraturePoint 5 179) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨179,by decide⟩).scale 1 12) = p5_179.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨179,by decide⟩
  have he : PointBox.calc p5_179.t = p5_179 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_180_contains : p5_180.Contains (quadraturePoint 5 180) := by
  have ht : p5_180.t.Contains (quadraturePoint 5 180) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨180,by decide⟩).scale 1 12) = p5_180.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨180,by decide⟩
  have he : PointBox.calc p5_180.t = p5_180 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_181_contains : p5_181.Contains (quadraturePoint 5 181) := by
  have ht : p5_181.t.Contains (quadraturePoint 5 181) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨181,by decide⟩).scale 1 12) = p5_181.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨181,by decide⟩
  have he : PointBox.calc p5_181.t = p5_181 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_182_contains : p5_182.Contains (quadraturePoint 5 182) := by
  have ht : p5_182.t.Contains (quadraturePoint 5 182) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨182,by decide⟩).scale 1 12) = p5_182.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨182,by decide⟩
  have he : PointBox.calc p5_182.t = p5_182 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_183_contains : p5_183.Contains (quadraturePoint 5 183) := by
  have ht : p5_183.t.Contains (quadraturePoint 5 183) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨183,by decide⟩).scale 1 12) = p5_183.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨183,by decide⟩
  have he : PointBox.calc p5_183.t = p5_183 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_184_contains : p5_184.Contains (quadraturePoint 5 184) := by
  have ht : p5_184.t.Contains (quadraturePoint 5 184) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨184,by decide⟩).scale 1 12) = p5_184.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨184,by decide⟩
  have he : PointBox.calc p5_184.t = p5_184 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_185_contains : p5_185.Contains (quadraturePoint 5 185) := by
  have ht : p5_185.t.Contains (quadraturePoint 5 185) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨185,by decide⟩).scale 1 12) = p5_185.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨185,by decide⟩
  have he : PointBox.calc p5_185.t = p5_185 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_186_contains : p5_186.Contains (quadraturePoint 5 186) := by
  have ht : p5_186.t.Contains (quadraturePoint 5 186) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨186,by decide⟩).scale 1 12) = p5_186.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨186,by decide⟩
  have he : PointBox.calc p5_186.t = p5_186 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_187_contains : p5_187.Contains (quadraturePoint 5 187) := by
  have ht : p5_187.t.Contains (quadraturePoint 5 187) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨187,by decide⟩).scale 1 12) = p5_187.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨187,by decide⟩
  have he : PointBox.calc p5_187.t = p5_187 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_188_contains : p5_188.Contains (quadraturePoint 5 188) := by
  have ht : p5_188.t.Contains (quadraturePoint 5 188) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨188,by decide⟩).scale 1 12) = p5_188.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨188,by decide⟩
  have he : PointBox.calc p5_188.t = p5_188 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_189_contains : p5_189.Contains (quadraturePoint 5 189) := by
  have ht : p5_189.t.Contains (quadraturePoint 5 189) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨189,by decide⟩).scale 1 12) = p5_189.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨189,by decide⟩
  have he : PointBox.calc p5_189.t = p5_189 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_190_contains : p5_190.Contains (quadraturePoint 5 190) := by
  have ht : p5_190.t.Contains (quadraturePoint 5 190) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨190,by decide⟩).scale 1 12) = p5_190.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨190,by decide⟩
  have he : PointBox.calc p5_190.t = p5_190 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p5_191_contains : p5_191.Contains (quadraturePoint 5 191) := by
  have ht : p5_191.t.Contains (quadraturePoint 5 191) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨191,by decide⟩).scale 1 12) = p5_191.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨191,by decide⟩
  have he : PointBox.calc p5_191.t = p5_191 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row5_11_contains_g_oai (k : Fin 16) : (row5_11 k).Contains (quadraturePoint 5 (176+k.val)) := by
  fin_cases k
  · exact p5_176_contains
  · exact p5_177_contains
  · exact p5_178_contains
  · exact p5_179_contains
  · exact p5_180_contains
  · exact p5_181_contains
  · exact p5_182_contains
  · exact p5_183_contains
  · exact p5_184_contains
  · exact p5_185_contains
  · exact p5_186_contains
  · exact p5_187_contains
  · exact p5_188_contains
  · exact p5_189_contains
  · exact p5_190_contains
  · exact p5_191_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row5_11_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row5_11_contains_g_oai
