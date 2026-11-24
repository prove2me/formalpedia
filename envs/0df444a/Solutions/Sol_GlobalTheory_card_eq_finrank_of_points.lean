-- Prove2me | solution 1 for GlobalTheory.card_eq_finrank_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:27.625153+00:00
-- url     : https://prove2.me/submissions/7d546be4-a542-4f05-aaa3-5e4dbef8afb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[R] E)) : Fintype.card ι = finrank R S := by
  have := (algebraMap R E).domain_nontrivial
  rw [← natCard_algHom_eq_finrank R S E, ← Nat.card_congr P, Nat.card_eq_fintype_card]
end GlobalTheory
