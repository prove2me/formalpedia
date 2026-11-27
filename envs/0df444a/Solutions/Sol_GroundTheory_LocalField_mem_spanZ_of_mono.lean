-- Prove2me | solution 1 for GroundTheory.LocalField.mem_spanZ_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:47:23.707014+00:00
-- url     : https://prove2.me/submissions/1303e450-8d3b-4440-b59c-aa25692c3bee

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Theorems.Thm_GroundTheory_LocalField_IsElementary_mono
import Theorems.Thm_GroundTheory_LocalField_one_mem_spanZ_of_mono
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono
import Theorems.Thm_GroundTheory_LocalField_mul_mem_spanZ


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
variable {G : Type u} [Group G] [Fintype G]
variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono
namespace GroundTheory.LocalField
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) : χ ∈ spanZ (IsElementary (G := G)) := by
  have h := mul_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono hχ (one_mem_spanZ_of_mono hmono)
  rwa [mul_one] at h
end GroundTheory.LocalField
