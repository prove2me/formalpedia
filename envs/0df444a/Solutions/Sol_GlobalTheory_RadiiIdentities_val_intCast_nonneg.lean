-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.val_intCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:22.355962+00:00
-- url     : https://prove2.me/submissions/f5d48c99-a247-4127-a970-be6603f63848

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Theorems.Thm_GlobalTheory_RadiiIdentities_val_natCast_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast val_natCast_nonneg v k
  · push_cast
    rw [AddValuation.map_neg]
    exact val_natCast_nonneg v k
end GlobalTheory.RadiiIdentities
