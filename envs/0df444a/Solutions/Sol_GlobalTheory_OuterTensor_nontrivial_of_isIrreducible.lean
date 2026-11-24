-- Prove2me | solution 1 for GlobalTheory.OuterTensor.nontrivial_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:28.479656+00:00
-- url     : https://prove2.me/submissions/b73258fb-3526-4824-95c2-028d03a71d5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleOuterTprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.OuterTensor
namespace GlobalTheory.OuterTensor
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
end GlobalTheory.OuterTensor
