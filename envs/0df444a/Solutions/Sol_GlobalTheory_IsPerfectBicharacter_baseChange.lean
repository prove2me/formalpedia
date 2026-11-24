-- Prove2me | solution 1 for GlobalTheory.IsPerfectBicharacter.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:52.178269+00:00
-- url     : https://prove2.me/submissions/1b9eed25-4206-460b-956e-5d88889d03b6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_pairingMap_pairingBaseChange
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
namespace GlobalTheory
namespace IsPerfectBicharacter
theorem _root_.solution (hu : IsPerfectBicharacter R u) :
    IsPerfectBicharacter A (pairingBaseChange A u) := by
  refine ⟨hu.toIsBicharacter.baseChange A, ?_⟩
  rw [← Function.Bijective.of_comp_iff _ (baseChangeLinear_bijective (R := R) (M := H) A)]
  have h : pairingMap A (pairingBaseChange A u) ∘ baseChangeLinear R A H =
      (LinearEquiv.ofBijective _ hu.bijective).baseChange R A _ _ :=
    funext (pairingMap_pairingBaseChange A u)
  rw [h]
  exact LinearEquiv.bijective _
end IsPerfectBicharacter
end GlobalTheory
