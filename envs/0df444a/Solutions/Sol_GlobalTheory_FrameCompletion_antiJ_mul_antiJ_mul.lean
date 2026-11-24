-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.antiJ_mul_antiJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:17:43.389993+00:00
-- url     : https://prove2.me/submissions/b224c42a-5e42-449f-aae4-a0e8112ce0ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self


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
variable {L : Type} [Field L] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {p : Type} (X : Matrix (Fin n) p L) : antiJ L n * (antiJ L n * X) = X := by
  rw [← Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
end GlobalTheory.FrameCompletion
