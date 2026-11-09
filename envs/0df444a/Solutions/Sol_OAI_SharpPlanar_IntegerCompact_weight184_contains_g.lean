-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weight184_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:51:46.33389+00:00
-- url     : https://prove2.me/submissions/a7877b2d-3780-4582-b0b5-87b2418b3cca

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightBoxCalc_contains_g

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

lemma fejerWeight_reverse (v : ℕ) (hv : v < 256) : fejerWeight (255-v) = fejerWeight v := by
  have hv' : v ≤ 255 := by omega
  have ha : fejerAngle (255-v) = Real.pi-fejerAngle v := by
    unfold fejerAngle
    rw [Nat.cast_sub hv']
    push_cast
    ring
  unfold fejerWeight
  rw [ha]
  congr 3
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [show 2*(a:ℝ)*(Real.pi-fejerAngle v)=(a:ℝ)*(2*Real.pi)-2*(a:ℝ)*fejerAngle v by ring]
  exact Real.cos_nat_mul_two_pi_sub _ a

end SharpPlanar

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma weight71_contains : weight71.Contains (fejerWeight 71) := by
  have he : weightBoxCalc 71 = weight71 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 71
lemma weight184_contains_g_oai : weight184.Contains (fejerWeight 184) := by
  rw [← fejerWeight_reverse 184 (by decide)]
  exact weight71_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weight184_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weight184_contains_g_oai
