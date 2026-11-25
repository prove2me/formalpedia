-- Prove2me | solution 1 for GroundTheory.LocalField.mul_mem_spanA_of_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:46.822463+00:00
-- url     : https://prove2.me/submissions/905b4af0-e8b1-48b0-a1b2-412a398ab551

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_mul_mem_spanZ_of_mem
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
theorem _root_.solution {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanZ E) :
    f * g ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [smul_mul_assoc]
    exact smul_mem_spanA ha (mul_mem_spanZ_of_mem hE hmono hg' hg)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx
end GroundTheory.LocalField
