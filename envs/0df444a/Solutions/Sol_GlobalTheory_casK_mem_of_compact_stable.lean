-- Prove2me | solution 1 for GlobalTheory.casK_mem_of_compact_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:44.00722+00:00
-- url     : https://prove2.me/submissions/e1dd0acd-1ccd-45c7-ac6d-ff6117cf5d0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) : ∀ x ∈ S, CasK ε E x ∈ S := by
  intro x hx
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hS _ _ h _ (hS _ _ h.symm _ hx)
  · simp
end GlobalTheory
