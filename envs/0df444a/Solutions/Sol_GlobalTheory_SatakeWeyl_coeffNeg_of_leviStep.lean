-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:29.16105+00:00
-- url     : https://prove2.me/submissions/a9990923-b2e7-45cc-903a-a729b9f43a26

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
import Theorems.Thm_GlobalTheory_SatakeWeyl_Neg_step
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : LeviStep → IndexTwo → IndexThree → CoeffNeg := by
  intro H H2 H3 L _ _ _ ϖ σ q n m hU hm hm' h hh a i hi t t' ht ht'
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  rcases (by omega : n = 2 * i.val + 2 ∨ n = 2 * i.val + 3) with hn | hn
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 2 hn ![0, 0] (by decide) ![1, -1] (by decide) (q ^ 2)
      (pow_ne_zero _ hq) (H2 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 3 hn ![0, 0, 0] (by decide) ![1, 0, -1] (by decide) (q ^ 4)
      (pow_ne_zero _ hq) (H3 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring
end GlobalTheory.SatakeWeyl
