-- Prove2me | solution 1 for GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:03.947061+00:00
-- url     : https://prove2.me/submissions/a97a5580-8600-4e02-a7f1-1b7b9ba70b7e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualWeylEqBotOfNotAntitone
import Theorems.Thm_GlobalTheory_NonDomZero_exists_lt_lt_of_not_antitone
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleNonDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonDomZero
namespace GlobalTheory.NonDomZero
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)
end GlobalTheory.NonDomZero
