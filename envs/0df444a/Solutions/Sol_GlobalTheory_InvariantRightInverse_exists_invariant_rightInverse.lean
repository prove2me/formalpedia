-- Prove2me | solution 1 for GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:26.61138+00:00
-- url     : https://prove2.me/submissions/26f18b50-6b94-45ba-b0a2-523d71b3acd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantRightInverseField
import Theorems.Thm_GlobalTheory_InvariantRightInverse_exists_invariant_rightInverse_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantRightInverse
namespace GlobalTheory.InvariantRightInverse
theorem _root_.solution :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  intro L _ hL G act N b _ _ _ _ κ Y h hκ
  letI : Field L := hL.toField
  exact exists_invariant_rightInverse_field G act N b κ Y h hκ
end GlobalTheory.InvariantRightInverse
