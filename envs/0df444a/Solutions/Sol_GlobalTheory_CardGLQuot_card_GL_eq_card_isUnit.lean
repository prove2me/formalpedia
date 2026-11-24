-- Prove2me | solution 1 for GlobalTheory.CardGLQuot.card_GL_eq_card_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:22.926264+00:00
-- url     : https://prove2.me/submissions/1b484140-6eec-4c4f-b613-bed43b7a9d62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot
open Classical
namespace GlobalTheory.CardGLQuot
theorem _root_.solution (S : Type) [CommRing S] [Fintype S] (n : ℕ) :
    Nat.card (GL (Fin n) S) =
      (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) S => IsUnit A)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun u => ⟨(u : Matrix (Fin n) (Fin n) S), u.isUnit⟩) ⟨?_, ?_⟩)
  · intro u v h; exact Units.ext (congrArg Subtype.val h)
  · rintro ⟨A, hA⟩; exact ⟨hA.unit, rfl⟩
end GlobalTheory.CardGLQuot
