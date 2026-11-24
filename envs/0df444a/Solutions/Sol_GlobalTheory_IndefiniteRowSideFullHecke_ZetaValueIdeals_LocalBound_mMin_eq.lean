-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.LocalBound.mMin_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:37.40542+00:00
-- url     : https://prove2.me/submissions/d5aa1090-f44e-46e5-976e-cc747265a7a7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
namespace LocalBound
theorem _root_.solution {k : ℕ} {z : ClassGroup (𝓞 F) → ℚ} {l : ℕ} (h : LocalBound k z l) :
    mMin l (finrank ℚ F * k) = Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k) := by
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h1 h2
  · exact h.2.2.2 h1
  · exact h.2.2.1 h1 h2
  · exact h.2.1 h1 h2
end LocalBound
end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
