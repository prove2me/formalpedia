-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Swap.ex_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:26.655464+00:00
-- url     : https://prove2.me/submissions/afd10a23-61b7-41e4-a68c-7a566febcef3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap
namespace GlobalTheory.SatakeWeyl.Swap
theorem _root_.solution {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (h : m ≤ c.val) (h' : c.val + m < n) :
    ex n m a c = 0 := by
  unfold ex
  rw [dif_neg (by omega), dif_neg (by omega)]
end GlobalTheory.SatakeWeyl.Swap
