-- Prove2me | solution 1 for GlobalTheory.DimDrop.finite_of_topologicalKrullDim_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:39.967488+00:00
-- url     : https://prove2.me/submissions/97a28d34-69f5-4661-804b-5d73d00b0b37

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
theorem _root_.solution (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 h
  have hcomp : ∀ x : S, closure ({x} : Set S) ∈ irreducibleComponents S := by
    intro x
    refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
    have := hm ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (b := ⟨closure T, hT.closure, isClosed_closure⟩) (fun y hy => subset_closure (hle hy))
    exact subset_closure.trans this
  haveI : Finite (irreducibleComponents S) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective (fun x => (⟨closure {x}, hcomp x⟩ : irreducibleComponents S))
    fun x y hxy => (inseparable_iff_closure_eq.2 (congrArg Subtype.val hxy)).eq
end GlobalTheory.DimDrop
