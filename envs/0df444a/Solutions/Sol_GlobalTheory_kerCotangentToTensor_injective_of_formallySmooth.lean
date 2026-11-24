-- Prove2me | solution 1 for GlobalTheory.kerCotangentToTensor_injective_of_formallySmooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:15.024057+00:00
-- url     : https://prove2.me/submissions/281c130c-ed77-45b4-9a71-611f4b19ff0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k R F : Type*) [CommRing k] [CommRing R]
    [CommRing F] [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra.FormallySmooth k F] (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm
    ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) _ hsurj ⟨2, hnil⟩⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)
end GlobalTheory
