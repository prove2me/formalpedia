-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:00.839968+00:00
-- url     : https://prove2.me/submissions/7fe64e43-b246-4656-b274-09ea58fe51bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution {ι κ ι' κ' : Type} {M : Matrix ι κ L} (hM : IsInt M) (f : ι' → ι) (g : κ' → κ) :
    IsInt (M.submatrix f g) := fun i j => hM (f i) (g j)
end GlobalTheory.FrameCompletion
