-- Prove2me | solution 1 for GlobalTheory.FinWeil.selfDual_map_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:58.02817+00:00
-- url     : https://prove2.me/submissions/66e7f9e5-8f5c-42e5-b9e2-43db679c530d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Theorems.Thm_GlobalTheory_FinWeil_rep_inv_apply
import Theorems.Thm_GlobalTheory_FinWeil_mem_map_rep

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
theorem _root_.solution {γ : X → X → ℂ} {Γ : Type} [Group Γ]
    (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (g : Γ) :
    _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) := by
  intro x
  rw [_root_.GlobalTheory.FinWeil.mem_map_rep, hA (ρ g⁻¹ x)]
  constructor
  · intro H b hb
    rw [← hρ g⁻¹]
    exact H _ ((_root_.GlobalTheory.FinWeil.mem_map_rep ρ g A b).1 hb)
  · intro H a ha
    have key := H (ρ g a) (Submodule.mem_map_of_mem ha)
    rwa [← hρ g⁻¹, _root_.GlobalTheory.FinWeil.rep_inv_apply] at key
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
