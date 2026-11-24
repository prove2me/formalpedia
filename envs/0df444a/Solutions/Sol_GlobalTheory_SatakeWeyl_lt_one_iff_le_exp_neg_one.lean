-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.lt_one_iff_le_exp_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:43.980722+00:00
-- url     : https://prove2.me/submissions/c325d4a8-5217-4990-af9a-36ff12155106

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] at h
end GlobalTheory.SatakeWeyl
