-- Prove2me | solution 1 for GroundTheory.LocalField.mul_mem_spanZ_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:36.083738+00:00
-- url     : https://prove2.me/submissions/216e71c8-12c7-4899-8f6e-953a66ab40b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_mul_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add


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
theorem _root_.solution {f g : G → ℂ} (hf : f ∈ spanZ E) (hg : g ∈ spanZ E) :
    f * g ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    exact mul_mem_spanZ hE hmono (IsCharacter.indLin K l) hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx
end GroundTheory.LocalField
