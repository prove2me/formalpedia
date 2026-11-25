-- Prove2me | solution 1 for GroundTheory.Global.moduleSection_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:05.196795+00:00
-- url     : https://prove2.me/submissions/dc1d0490-7170-4404-803f-ebde19fe2c8b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (w w' : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    moduleSection w t * (moduleSection w' t)⁻¹ ∈ normOneSubgroup K := by
  rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection,
    ideleModule_moduleSection, mul_inv_cancel]
end GroundTheory.Global
