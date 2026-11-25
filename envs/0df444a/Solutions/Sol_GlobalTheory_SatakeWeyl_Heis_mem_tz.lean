-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.mem_tz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:03.363444+00:00
-- url     : https://prove2.me/submissions/baedf1c9-6043-4a7f-beaf-549c9816b026

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
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (y : L) : y ∈ (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔
    y ∈ intL L ∧ σ y + y = 0 := Iff.rfl
end GlobalTheory.SatakeWeyl.Heis
