-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubsetSum.exists_fin_enum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:19.686675+00:00
-- url     : https://prove2.me/submissions/a430508d-6389-45b2-98fc-db3b9782453d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum
namespace GlobalTheory.CompanionTheory.SubsetSum
theorem _root_.solution {R : Type*} (M : Multiset R) (n : ℕ) (h : Multiset.card M = n) :
    ∃ x : Fin n → R, Finset.univ.val.map x = M := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep M
  have h' : l.length = n := h
  subst h'
  refine ⟨l.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get]
  rfl
end GlobalTheory.CompanionTheory.SubsetSum
