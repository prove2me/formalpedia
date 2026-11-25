-- Prove2me | solution 1 for GroundTheory.LocalField.brauerFun_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:43.50795+00:00
-- url     : https://prove2.me/submissions/47e5e556-dbd9-405c-ba6a-909852c0eb6a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_indFun_theta_mem_spanA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono
omit hp
namespace GroundTheory.LocalField
theorem _root_.solution : brauerFun p ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  refine Submodule.sum_mem _ fun c _ ↦ ?_
  split_ifs with h
  · exact indFun_theta_mem_spanA hζ hmono h
  · exact Submodule.zero_mem _
end GroundTheory.LocalField
