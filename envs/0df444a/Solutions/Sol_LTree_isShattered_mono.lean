-- Prove2me | solution 1 for LTree.isShattered_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:39.609349+00:00
-- url     : https://prove2.me/submissions/1cfe6727-e2b5-409e-a91d-c0648c8f3d00

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
namespace LTree
theorem _root_.solution {X : Type} {n : ℕ} (T : LTree X n)
    {C C' : ConceptClass X Bool} (h : C ⊆ C') :
    T.isShattered C → T.isShattered C' := by
  induction T generalizing C C' with
  | leaf => exact Set.Nonempty.mono h
  | branch x l r ihl ihr =>
    intro ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩
    refine ⟨⟨ct, h hct, hctx⟩, ⟨cf, h hcf, hcfx⟩, ?_, ?_⟩
    · exact ihl (fun _ hm => ⟨h hm.1, hm.2⟩) hsl
    · exact ihr (fun _ hm => ⟨h hm.1, hm.2⟩) hsr
end LTree
