-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_tensor_quotient_under
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:23.450669+00:00
-- url     : https://prove2.me/submissions/06bbc596-f830-4edf-8e46-315066440551

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_under_eq_of_mem_associatedPrimes_tensor_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] {N : Type*}
    [AddCommGroup N] [Module A N] [hN : Module.Finite A N] {q : Ideal B}
    (hq : q ∈ associatedPrimes B (M ⊗[A] N)) :
    q ∈ associatedPrimes B (M ⊗[A] (A ⧸ q.under A)) := by
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [associatedPrimes.eq_empty_of_subsingleton] at hq
  | quotient N p e =>
    rw [LinearEquiv.AssociatedPrimes.eq
      (AlgebraTensorModule.congr (LinearEquiv.refl B M) e)] at hq
    rwa [under_eq_of_mem_associatedPrimes_tensor_quotient p.asIdeal hq]
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    have hf' : Function.Injective (AlgebraTensorModule.lTensor B M f) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hf
    have hfg' : Function.Exact (AlgebraTensorModule.lTensor B M f)
        (AlgebraTensorModule.lTensor B M g) := lTensor_exact M hfg hg
    exact (associatedPrimes.subset_union_of_exact hf' hfg' hq).elim h₁ h₃
end GlobalTheory
