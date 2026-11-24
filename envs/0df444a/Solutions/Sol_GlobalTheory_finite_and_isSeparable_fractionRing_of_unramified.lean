-- Prove2me | solution 1 for GlobalTheory.finite_and_isSeparable_fractionRing_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:54.335173+00:00
-- url     : https://prove2.me/submissions/9217204a-2f15-4fd1-85a5-83ca497caffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution (R B K L : Type*) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.EssFiniteType R B] [Algebra.FormallyUnramified R B]
    [Field K] [Field L] [Algebra R K] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L] :
    Module.Finite K L ∧ Algebra.IsSeparable K L := by
  have : Algebra.EssFiniteType B L := .of_isLocalization L (nonZeroDivisors B)
  have : Algebra.FormallyUnramified B L := .of_isLocalization (nonZeroDivisors B)
  have : Algebra.EssFiniteType R L := .comp R B L
  have : Algebra.FormallyUnramified R L := .comp R B L
  have : Algebra.EssFiniteType K L := .of_comp R K L
  have : Algebra.FormallyUnramified K L := .of_restrictScalars R K L
  exact ⟨Algebra.FormallyUnramified.finite_of_free K L, Algebra.FormallyUnramified.isSeparable K L⟩
end GlobalTheory
