-- Prove2me | solution 1 for OAI.SharpPlanar.cached_density_rule_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:36:07.674421+00:00
-- url     : https://prove2.me/submissions/944fbcf5-d60a-4697-8c44-e87dfcf54075

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_sum_fin_square_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_finSum_contains_e

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

lemma cached_density_rule_contains_e_oai
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hc : ∀ j i v, (c j i v).Contains ((fejerWeight (16*i.val+v.val):ℂ)*
      f j.val (quadraturePoint j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains (g (quadraturePoint j.val (16*i.val+v.val)))) :
    (cachedMomentRuleBox c k).Contains
      (∑ j : Fin 6, pieceRule (fun t => f j.val t*g t) j.val) := by
  unfold cachedMomentRuleBox pieceRule
  apply finSum_contains_e
  intro j
  have ht (v : ℕ) : diskAffine j.val (fejerNode v) = (quadraturePoint j.val v:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  simp_rw [ht]
  rw [← sum_fin_square_e 16 (fun v => (fejerWeight v:ℂ)*(f j.val (quadraturePoint j.val v)*g (quadraturePoint j.val v)))]
  have hh := finSum_contains_e (fun i => finSum_contains_e (fun v => CBox.contains_mul_e (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale_e hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,mul_assoc] using hs

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.cached_density_rule_contains_e_oai := @OAI.SharpPlanar.cached_density_rule_contains_e_oai
