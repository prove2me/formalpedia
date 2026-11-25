-- Prove2me | solution 1 for GroundTheory.LocalField.pow_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:36.992187+00:00
-- url     : https://prove2.me/submissions/640a8209-3fc4-4ea7-9d81-6cfdb9fbde80

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_mul_mem_spanA

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
variable {G : Type*} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hE hmono
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) {M : ℕ} (hM : M ≠ 0) :
    f ^ M ∈ spanA E ζ := by
  induction M with
  | zero => exact absurd rfl hM
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM'
    · simpa using hf
    · rw [pow_succ]
      exact mul_mem_spanA hE hmono (ih hM'.ne') hf
end GroundTheory.LocalField
