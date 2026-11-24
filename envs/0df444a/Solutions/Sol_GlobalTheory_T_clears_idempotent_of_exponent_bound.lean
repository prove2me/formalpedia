-- Prove2me | solution 1 for GlobalTheory.T.clears_idempotent_of_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:21.637912+00:00
-- url     : https://prove2.me/submissions/f35e44d1-d535-4796-8d66-6ee0ee0df81d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBoundStatement
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_clearsIdem_condC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) := by
  first | exact @GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC | exact GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC | (intros; apply GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC <;> assumption)
end _root_.GlobalTheory.T
