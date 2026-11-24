-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.sum_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:50.783816+00:00
-- url     : https://prove2.me/submissions/7f4a837e-7de7-4362-bfd5-4859d5f42a07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_GlobalTheory_CharacterSumInverse_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open GlobalTheory.FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]
variable [Fintype T] (ρ : Representation o T M) (u : o)
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)]
    (hu : u * (Fintype.card T : o) = 1) (x : M) : ∑ c : T →* oˣ, avg ρ u c x = x := by
  first
  | exact @_root_.GlobalTheory.CharacterSumInverse.main
  | exact _root_.GlobalTheory.CharacterSumInverse.main
  | (apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharacterSumInverse.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharacterSumInverse.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharacterSumInverse.main ..)
end GlobalTheory.FiniteAbelianWeights
