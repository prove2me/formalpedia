-- Prove2me | solution 1 for GlobalTheory.FinWeil.isHeis_comp_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:54.19981+00:00
-- url     : https://prove2.me/submissions/efbbebc8-056b-4da0-bfd1-c8bbaa3d2ac5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.FinWeil
namespace _root_.GlobalTheory.FinWeil
theorem _root_.solution {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) (g : Γ) :
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ (fun x => W (ρ g x)) := by
  refine ⟨h.sg_sg, h.w_add,
    h.add_left, h.add_right,
    h.alt, h.adj, fun v => ?_,
    fun x y v => ?_⟩
  · show W (ρ g 0) v = v
    rw [map_zero, h.zero]
  · show W (ρ g x) (W (ρ g y) v) = γ (w • x) y • W (ρ g (x + y)) v
    rw [h.comp, map_add, ← hρ g (w • x) y, LinearMap.map_smul]
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
