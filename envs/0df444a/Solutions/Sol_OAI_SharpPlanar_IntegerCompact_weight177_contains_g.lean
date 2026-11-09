-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weight177_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:50:31.257714+00:00
-- url     : https://prove2.me/submissions/e5ea60a3-72d4-4931-85f7-a3fd962ee3d0

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
lemma weight78_contains : weight78.Contains (fejerWeight 78) := by
  have he : weightBoxCalc 78 = weight78 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 78
lemma weight177_contains_g_oai : weight177.Contains (fejerWeight 177) := by
  rw [← fejerWeight_reverse 177 (by decide)]
  exact weight78_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weight177_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weight177_contains_g_oai
