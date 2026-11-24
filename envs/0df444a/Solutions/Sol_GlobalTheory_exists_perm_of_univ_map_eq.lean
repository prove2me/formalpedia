-- Prove2me | solution 1 for GlobalTheory.exists_perm_of_univ_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:49.120988+00:00
-- url     : https://prove2.me/submissions/3a180229-f771-4380-bad1-771ce345fb8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymmetricFunctionInverseInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end GlobalTheory
