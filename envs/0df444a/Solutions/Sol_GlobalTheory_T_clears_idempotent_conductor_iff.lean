-- Prove2me | solution 1 for GlobalTheory.T.clears_idempotent_conductor_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:20.173198+00:00
-- url     : https://prove2.me/submissions/887dc0a5-e89e-4c60-b4ea-32b7d7925fed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIffStatement
import Theorems.Thm_GlobalTheory_CondAway_clearsIdem_condQ_iff


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  first | exact @GlobalTheory.CondAway.clearsIdem_condQ_iff | exact GlobalTheory.CondAway.clearsIdem_condQ_iff | (intros; apply GlobalTheory.CondAway.clearsIdem_condQ_iff <;> assumption)
end _root_.GlobalTheory.T
