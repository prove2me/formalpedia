-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:57.101139+00:00
-- url     : https://prove2.me/submissions/e150a4c8-3768-4dae-ae27-79d963e7f75e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_indFun_subtype_indLin
import Theorems.Thm_GroundTheory_LocalField_indLin_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_nat
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


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
theorem _root_.solution {K : Subgroup G} (hK : E K) {χ : K → ℂ} (hχ : IsCharacter χ) :
    indFun K.subtype χ ∈ spanZ E := by
  classical
  obtain ⟨m, hm⟩ := hχ.exists_nat
  rw [hm, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  obtain ⟨L, μ, hLμ⟩ := hmono K hK ψ (mem_irrChars.mp hψ)
  rw [map_smul, Nat.cast_smul_eq_nsmul ℂ, hLμ, indFun_subtype_indLin]
  exact Submodule.smul_of_tower_mem _ _
    (indLin_mem_spanZ (hE K _ hK (Subgroup.map_subtype_le L)) _)
end GroundTheory.LocalField
