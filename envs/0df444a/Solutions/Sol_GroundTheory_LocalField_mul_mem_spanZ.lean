-- Prove2me | solution 1 for GroundTheory.LocalField.mul_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:14.83299+00:00
-- url     : https://prove2.me/submissions/1ee0c8bb-c942-49a1-adca-6dbdc037c197

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_indFun_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_mul
import Theorems.Thm_GroundTheory_LocalField_indFun_mul_comp


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
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) {f : G → ℂ} (hf : f ∈ spanZ E) :
    χ * f ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    rw [mul_comm, indLin, ← indFun_mul_comp _ _ hχ.isClassFun]
    exact indFun_mem_spanZ hE hmono hK ((isCharacter_monoidHom l).mul (hχ.comp K.subtype))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hx
end GroundTheory.LocalField
