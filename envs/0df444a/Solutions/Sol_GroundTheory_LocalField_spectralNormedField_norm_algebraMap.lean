-- Prove2me | solution 1 for GroundTheory.LocalField.spectralNormedField_norm_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:27.488067+00:00
-- url     : https://prove2.me/submissions/44bdf100-297a-4ce9-9ad6-f843938d5eb1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension

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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (a : K) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := normedField K
  exact spectralNorm_extends a
end GroundTheory.LocalField
