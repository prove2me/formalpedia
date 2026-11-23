-- Prove2me | solution 1 for GlobalTheory.FinWeil.mem_map_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:34.337979+00:00
-- url     : https://prove2.me/submissions/6325c618-92ee-4861-88e5-5d384deae3c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Theorems.Thm_GlobalTheory_FinWeil_rep_inv_apply

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
theorem _root_.solution {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X) (g : Γ)
    (A : Submodule R X) (x : X) :
    x ∈ A.map (ρ g) ↔ ρ g⁻¹ x ∈ A := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [_root_.GlobalTheory.FinWeil.rep_inv_apply]
  · intro hx
    refine ⟨ρ g⁻¹ x, hx, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
