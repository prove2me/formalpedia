-- Prove2me | solution 1 for GroundTheory.LocalField.integer_smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:30.806263+00:00
-- url     : https://prove2.me/submissions/e7fd5541-5592-4d86-973e-be3908b28161

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_eq

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
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution {c : 𝒪[K]} (hc : c ≠ 0) {y z : L} (h : c • y = c • z) : y = z := by
  rw [integer_smul_eq, integer_smul_eq] at h
  refine mul_left_cancel₀ ?_ h
  rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
  exact fun h0 => hc (Subtype.ext h0)
end GroundTheory.LocalField
