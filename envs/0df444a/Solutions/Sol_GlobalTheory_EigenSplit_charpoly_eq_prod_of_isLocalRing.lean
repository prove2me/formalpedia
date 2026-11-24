-- Prove2me | solution 1 for GlobalTheory.EigenSplit.charpoly_eq_prod_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:44.529728+00:00
-- url     : https://prove2.me/submissions/90ae0d0b-fcf4-49d2-b873-3fbaf30aa65a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_free_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution [IsLocalRing R] (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i)) :=
  charpoly_eq_prod h ρ (free_eigenSub h ρ) a
end GlobalTheory.EigenSplit
