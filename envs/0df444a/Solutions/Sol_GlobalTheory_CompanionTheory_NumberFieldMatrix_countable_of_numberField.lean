-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:01.045226+00:00
-- url     : https://prove2.me/submissions/a61ebfce-2a6e-42c1-8635-50d1d654f245

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountableOfNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NumberFieldMatrix
namespace GlobalTheory.CompanionTheory.NumberFieldMatrix
theorem _root_.solution (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable
end GlobalTheory.CompanionTheory.NumberFieldMatrix
