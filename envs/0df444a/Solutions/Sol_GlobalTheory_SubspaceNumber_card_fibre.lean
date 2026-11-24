-- Prove2me | solution 1 for GlobalTheory.SubspaceNumber.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:47.045318+00:00
-- url     : https://prove2.me/submissions/ff2e32d4-c162-45fe-9316-278f3e44dfa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.SubspaceNumber
namespace GlobalTheory.SubspaceNumber
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by
  symm
  have hspan : ∀ t : Fin a → W, LinearIndependent F t →
      Submodule.span F (Set.range (W.subtype ∘ t)) = W := by
    intro t ht
    have h1 : Submodule.span F (Set.range t) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    rw [Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)
  · intro t u h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun x => x.1.1) h) i
  · rintro ⟨⟨s, hs⟩, h⟩
    have hm : ∀ i, s i ∈ W := fun i => by
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩
end GlobalTheory.SubspaceNumber
