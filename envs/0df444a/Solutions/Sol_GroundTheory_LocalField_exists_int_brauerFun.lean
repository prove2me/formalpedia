-- Prove2me | solution 1 for GroundTheory.LocalField.exists_int_brauerFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:16:34.515356+00:00
-- url     : https://prove2.me/submissions/c0d8f684-3356-436c-8897-eedcc77dae37

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_exists_int_indFun_theta

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
theorem _root_.solution (g : G) : ∃ k : ℤ, brauerFun p g = k := by
  have h : ∀ c : ConjClasses G, ∃ k : ℤ, (if (orderOf (classRep c)).Coprime p then
      indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0) g = k := by
    intro c
    split_ifs with h
    · exact exists_int_indFun_theta hζ hmono h g
    · exact ⟨0, by simp⟩
  choose k hk using h
  refine ⟨∑ c, k c, ?_⟩
  rw [brauerFun, Finset.sum_apply]
  push_cast
  exact Finset.sum_congr rfl fun c _ ↦ hk c
end GroundTheory.LocalField
