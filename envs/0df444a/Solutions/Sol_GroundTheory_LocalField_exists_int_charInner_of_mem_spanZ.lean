-- Prove2me | solution 1 for GroundTheory.LocalField.exists_int_charInner_of_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:32.029228+00:00
-- url     : https://prove2.me/submissions/89ab7bcd-e7da-4596-80aa-4623ac227447

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter


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
variable (E : Subgroup G → Prop)
variable {E}
namespace GroundTheory.LocalField
theorem _root_.solution {f : G → ℂ} (hf : f ∈ spanZ E) {ψ : G → ℂ}
    (hψ : IsIrrCharacter ψ) : ∃ k : ℤ, charInner G f ψ = k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    obtain ⟨n, hn⟩ := (IsCharacter.indLin K l).exists_nat_charInner hψ.isCharacter
    exact ⟨n, by rw [hn]; simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, LinearMap.add_apply, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨n * a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, ha, smul_eq_mul]
    push_cast
    ring
end GroundTheory.LocalField
