-- Prove2me | solution 1 for GlobalTheory.EtaleFibre.card_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:17.761831+00:00
-- url     : https://prove2.me/submissions/57bc16c1-64c9-49c0-a137-d7e27edb79bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleFibreEmbeddingsCard
import Theorems.Thm_GlobalTheory_EtaleFibre_finrank_baseChange_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaleFibre
namespace GlobalTheory.EtaleFibre
theorem _root_.solution (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] [Field L] [IsSepClosed L] [Algebra A L] :
    Finite (B →ₐ[A] L) ∧ Nat.card (B →ₐ[A] L) = Module.finrank A B := by
  have : IsArtinianRing (L ⊗[A] B) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[A] B))
  have e : (B →ₐ[A] L) ≃ PrimeSpectrum (L ⊗[A] B) :=
    (AlgHom.liftEquiv A L B L).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[A] B))
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, ← finrank_baseChange_field A B L,
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[A] B)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
end GlobalTheory.EtaleFibre
