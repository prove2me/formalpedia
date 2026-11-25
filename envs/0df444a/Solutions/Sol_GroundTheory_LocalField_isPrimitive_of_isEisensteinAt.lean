-- Prove2me | solution 1 for GroundTheory.LocalField.isPrimitive_of_isEisensteinAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:04:00.783797+00:00
-- url     : https://prove2.me/submissions/fd8f4bfc-eb6b-4b53-8ffa-0323c569a367

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein

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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : f.IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  exact isUnit_of_dvd_unit (hr _) (isUnit_leadingCoeff_of_isEisensteinAt hf)
end GroundTheory.LocalField
