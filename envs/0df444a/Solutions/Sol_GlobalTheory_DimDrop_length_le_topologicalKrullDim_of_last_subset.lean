-- Prove2me | solution 1 for GlobalTheory.DimDrop.length_le_topologicalKrullDim_of_last_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:41.324799+00:00
-- url     : https://prove2.me/submissions/99a52331-247c-42e0-8db5-a1d318546156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace Order
open GlobalTheory GlobalTheory.DimDrop
namespace GlobalTheory.DimDrop
theorem _root_.solution {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hsub : ∀ i, (q i : Set X) ⊆ Z := fun i x hx => h (q.monotone (Fin.le_last i) hx)
  have irr : ∀ i, IsIrreducible (Subtype.val ⁻¹' (q i : Set X) : Set Z) := by
    intro i
    haveI : IrreducibleSpace (q i : Set X) := Subtype.irreducibleSpace (q i).isIrreducible
    have := (IrreducibleSpace.isIrreducible_univ (q i : Set X)).image (Set.inclusion (hsub i))
      (continuous_inclusion (hsub i)).continuousOn
    rw [Set.image_univ, Set.range_inclusion] at this
    exact this
  let f : Fin (q.length + 1) → IrreducibleCloseds Z := fun i =>
    ⟨Subtype.val ⁻¹' (q i : Set X), irr i, (q i).isClosed.preimage continuous_subtype_val⟩
  have hf : ∀ i j, f i = f j → q i = q j := by
    intro i j e
    have e' : (Subtype.val ⁻¹' (q i : Set X) : Set Z) = Subtype.val ⁻¹' (q j : Set X) :=
      congrArg SetLike.coe e
    have e'' := congrArg (Set.image (Subtype.val : Z → X)) e'
    rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (hsub i), Set.inter_eq_right.2 (hsub j)] at e''
    exact SetLike.coe_injective e''
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := q.length
      toFun := f
      step := fun i => by
        have hs : q i.castSucc < q i.succ := q.step i
        show f i.castSucc < f i.succ
        refine lt_of_le_of_ne ?_ fun e => hs.ne (hf _ _ e)
        intro x hx
        exact hs.le hx }
  exact LTSeries.length_le_krullDim p
end GlobalTheory.DimDrop
