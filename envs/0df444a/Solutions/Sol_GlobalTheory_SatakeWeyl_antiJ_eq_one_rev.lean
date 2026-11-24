-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.antiJ_eq_one_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:32.542898+00:00
-- url     : https://prove2.me/submissions/6298f989-ffe7-4e48-b355-8167b275afb4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_antiJ_mul_apply


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
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i.rev = j then 1 else 0 := by
  have := antiJ_mul_apply (1 : Matrix (Fin n) (Fin n) L) i j
  rw [Matrix.mul_one] at this
  rw [this, Matrix.one_apply]
end GlobalTheory.SatakeWeyl
