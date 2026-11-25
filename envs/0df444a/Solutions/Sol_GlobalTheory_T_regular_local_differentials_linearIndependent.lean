-- Prove2me | solution 1 for GlobalTheory.T.regular_local_differentials_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:29.473849+00:00
-- url     : https://prove2.me/submissions/ad196061-9874-4bbb-b762-659665acc9be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularLocalDifferentialsBasis
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_RegularLocalDifferentialsLinearIndependent
import Theorems.Thm_GlobalTheory_linearIndependent_tmul_D_of_regular_system


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  first | exact @_root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | exact _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | (intros; apply _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system <;> assumption)
end _root_.GlobalTheory.T
