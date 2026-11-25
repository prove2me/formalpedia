-- Prove2me | solution 1 for GlobalTheory.T.invertible_of_faithfully_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:44.612343+00:00
-- url     : https://prove2.me/submissions/22ff0002-0052-4721-8d54-44be1e25004c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlatStatement
import Theorems.Thm_GlobalTheory_FFDescent_invertible_of_invertible_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  first | exact @GlobalTheory.FFDescent.invertible_of_invertible_baseChange | exact GlobalTheory.FFDescent.invertible_of_invertible_baseChange | (intros; apply GlobalTheory.FFDescent.invertible_of_invertible_baseChange <;> assumption)
end _root_.GlobalTheory.T
