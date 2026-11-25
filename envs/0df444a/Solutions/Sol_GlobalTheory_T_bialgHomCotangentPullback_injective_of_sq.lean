-- Prove2me | solution 1 for GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:43.068835+00:00
-- url     : https://prove2.me/submissions/23b07712-fe33-4445-971f-a5b34e606d08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSqStatement
import Theorems.Thm_GlobalTheory_PDiv_cotMap_injective_of_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)
end _root_.GlobalTheory.T
