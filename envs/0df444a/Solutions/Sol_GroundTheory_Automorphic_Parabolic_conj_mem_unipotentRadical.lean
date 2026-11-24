-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.conj_mem_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:03.459289+00:00
-- url     : https://prove2.me/submissions/29cf7fd2-0f71-4c3f-8e16-0b24cedb81b0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentRadical_le_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical_iff_leviProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {p u : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hu : u ∈ unipotentRadical F n β) : p * u * p⁻¹ ∈ unipotentRadical F n β := by
  have huP := unipotentRadical_le_blockUpper hu
  have h := (mem_unipotentRadical_iff_leviProj (p := ⟨u, huP⟩)).1 hu
  have hm : p * u * p⁻¹ ∈ blockUpper F n β :=
    (blockUpper F n β).mul_mem ((blockUpper F n β).mul_mem hp huP) ((blockUpper F n β).inv_mem hp)
  refine (mem_unipotentRadical_iff_leviProj (p := ⟨_, hm⟩)).2 ?_
  have : (⟨p * u * p⁻¹, hm⟩ : blockUpper F n β) = ⟨p, hp⟩ * ⟨u, huP⟩ * (⟨p, hp⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]
end GroundTheory.Automorphic.Parabolic
