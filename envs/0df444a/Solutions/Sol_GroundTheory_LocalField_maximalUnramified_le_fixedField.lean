-- Prove2me | solution 1 for GroundTheory.LocalField.maximalUnramified_le_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:58.678022+00:00
-- url     : https://prove2.me/submissions/4bf9ce17-246b-4d4d-a985-5184f433b5a6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_inertiaSubgroup_apply_eq

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
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by
  obtain ⟨β, P, -, hβ, hd, heq, -, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq, IntermediateField.adjoin_simple_le_iff]
  exact fun σ ↦ inertiaSubgroup_apply_eq K L σ σ.2 P β hβ hd
end GroundTheory.LocalField
