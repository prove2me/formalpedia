-- Prove2me | solution 1 for GlobalTheory.FFDescent.invertible_of_invertible_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:30:58.144805+00:00
-- url     : https://prove2.me/submissions/ea9660e4-2e21-40df-8e7b-05db11462876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
import Theorems.Thm_GlobalTheory_FlatDescent_invertible_baseChange_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.FFDescent
namespace GlobalTheory.FFDescent
theorem _root_.solution : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  intro B B' _ _ _ _ _ M _ _ h
  exact (GlobalTheory.FlatDescent.invertible_baseChange_iff B' M).1 h
end GlobalTheory.FFDescent
