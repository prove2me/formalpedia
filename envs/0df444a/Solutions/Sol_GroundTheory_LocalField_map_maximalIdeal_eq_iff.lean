-- Prove2me | solution 1 for GroundTheory.LocalField.map_maximalIdeal_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:56.363433+00:00
-- url     : https://prove2.me/submissions/9e0fc34d-f383-44e3-a563-e72fa894a2de

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_ne_bot
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos


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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] ↔ IsUnramified K L := by
  rw [map_maximalIdeal K L, isUnramified_iff]
  constructor
  · intro h
    have hpos := ramificationIndex_pos K L
    by_contra hne
    have h2 : 2 ≤ ramificationIndex K L := by omega
    have hL : maximalIdeal 𝒪[L] ≠ ⊥ := maximalIdeal_ne_bot L
    have hlt := Ideal.pow_succ_lt_pow hL 1
    have hle : maximalIdeal 𝒪[L] ^ 1 ≤ maximalIdeal 𝒪[L] ^ (1 + 1) :=
      calc maximalIdeal 𝒪[L] ^ 1 = maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
            rw [pow_one, h]
        _ ≤ maximalIdeal 𝒪[L] ^ (1 + 1) := Ideal.pow_le_pow_right h2
    exact absurd hle (not_le_of_gt hlt)
  · intro h
    rw [h, pow_one]
end GroundTheory.LocalField
