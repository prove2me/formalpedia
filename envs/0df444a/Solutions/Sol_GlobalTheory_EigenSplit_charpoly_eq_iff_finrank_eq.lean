-- Prove2me | solution 1 for GlobalTheory.EigenSplit.charpoly_eq_iff_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:19.509932+00:00
-- url     : https://prove2.me/submissions/b8528b8f-5aa1-4b6b-b150-27744bb63bd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_free_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod_of_isLocalRing
import Theorems.Thm_GlobalTheory_EigenSplit_finrank_eq_of_charpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

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
theorem _root_.solution [IsLocalRing R] (r : ι → ℕ) :
    (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
      ∀ i, Module.finrank R (eigenSub ρ (σ i)) = r i :=
  ⟨finrank_eq_of_charpoly h ρ (free_eigenSub h ρ) r, fun hr a => by
    rw [charpoly_eq_prod_of_isLocalRing h ρ]; simp only [hr]⟩
end GlobalTheory.EigenSplit
