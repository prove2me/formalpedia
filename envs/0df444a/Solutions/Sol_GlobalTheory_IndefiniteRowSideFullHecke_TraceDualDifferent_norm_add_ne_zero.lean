-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.norm_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:56.978487+00:00
-- url     : https://prove2.me/submissions/d1967c2e-8808-43c5-a70e-688293d1d0e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
theorem _root_.solution {z : (F →+* ℝ) → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) (a : F) :
    ∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ h => hz τ (by simpa using congrArg Complex.im h)
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
