-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.heis_01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:18.196807+00:00
-- url     : https://prove2.me/submissions/99fe7dd7-164f-41e9-aa5d-bf0e4363d2c9

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (x y : L) : Heisenberg₂ σ x y 0 1 = x := rfl
end GlobalTheory.SatakeWeyl.Heis
