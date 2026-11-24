-- Prove2me | solution 1 for GlobalTheory.BorelUMod.UpLatIndex.ordBall_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:48.606897+00:00
-- url     : https://prove2.me/submissions/0eefd4c1-01cc-4d04-bb85-42611dab3a27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod.UpLatIndex
theorem _root_.solution {k K : ℤ} (h : k ≤ K) : ordBall L K ≤ ordBall L k :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.2 (neg_le_neg h))
end GlobalTheory.BorelUMod.UpLatIndex
