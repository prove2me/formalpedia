-- Prove2me | solution 1 for GroundTheory.LocalField.map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:10.459002+00:00
-- url     : https://prove2.me/submissions/d937b623-d256-4212-9da0-8271a056f8cd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_ne_bot

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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) =
      IsLocalRing.maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
  have hne : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (maximalIdeal_ne_bot K)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ hne
  have hL : IsLocalRing.maximalIdeal 𝒪[L] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have h : (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx' (IsLocalRing.maximalIdeal 𝒪[L]) = n :=
    Ideal.ramificationIdx'_spec hn.le (by
      rw [hn]
      exact not_le_of_gt (Ideal.pow_succ_lt_pow hL n))
  rw [ramificationIndex, ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_ne_bot K), h,
    hn]
end GroundTheory.LocalField
