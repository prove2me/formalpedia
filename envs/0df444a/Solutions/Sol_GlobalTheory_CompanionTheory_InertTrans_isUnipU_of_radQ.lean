-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.isUnipU_of_radQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:54.719625+00:00
-- url     : https://prove2.me/submissions/d91d57a8-eb3f-4872-bc0f-2ea4c81e2a4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_blk_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : IsUnipU u := by
  have hB : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (hB i j (blk_mono h)).trans (Matrix.one_apply_ne (ne_of_gt h))
  · exact (hB i i le_rfl).trans (Matrix.one_apply_eq i)
end GlobalTheory.CompanionTheory.InertTrans
