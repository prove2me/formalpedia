-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:20.466909+00:00
-- url     : https://prove2.me/submissions/b8c00217-2b3e-4296-9b53-aefd5070394e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution {L : Type*} [Field L] {S : Set L} {p : L[X]}
    (hp : p ≠ 0) (hS : ∀ x ∈ S, p.eval x = 0) : S.Finite ∧ S.ncard ≤ p.natDegree := by
  classical
  have hsub : S ⊆ (p.roots.toFinset : Set L) := fun x hx => by
    simp [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, hS x hx]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc S.ncard ≤ (p.roots.toFinset : Set L).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
end GlobalTheory.MinpolyHeightCount
