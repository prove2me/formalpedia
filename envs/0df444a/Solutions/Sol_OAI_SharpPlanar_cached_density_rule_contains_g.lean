-- Prove2me | solution 1 for OAI.SharpPlanar.cached_density_rule_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:11.821884+00:00
-- url     : https://prove2.me/submissions/6d2c4b8a-e41e-459d-91c2-355109e2b075
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_sum_fin_square_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add_g (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

lemma cached_density_rule_contains_g_oai
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hc : ∀ j i v, (c j i v).Contains ((fejerWeight (16*i.val+v.val):ℂ)*
      f j.val (quadraturePoint j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains (g (quadraturePoint j.val (16*i.val+v.val)))) :
    (cachedMomentRuleBox c k).Contains
      (∑ j : Fin 6, pieceRule (fun t => f j.val t*g t) j.val) := by
  unfold cachedMomentRuleBox pieceRule
  apply finSum_contains
  intro j
  have ht (v : ℕ) : diskAffine j.val (fejerNode v) = (quadraturePoint j.val v:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  simp_rw [ht]
  rw [← sum_fin_square_g 16 (fun v => (fejerWeight v:ℂ)*(f j.val (quadraturePoint j.val v)*g (quadraturePoint j.val v)))]
  have hh := finSum_contains (fun i => finSum_contains (fun v => CBox.contains_mul_g (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale_g hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,mul_assoc] using hs

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.cached_density_rule_contains_g_oai := @OAI.SharpPlanar.cached_density_rule_contains_g_oai
