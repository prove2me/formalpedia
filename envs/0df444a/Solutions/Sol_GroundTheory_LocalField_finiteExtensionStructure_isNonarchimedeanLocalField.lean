-- Prove2me | solution 1 for GroundTheory.LocalField.finiteExtensionStructure_isNonarchimedeanLocalField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:48.416816+00:00
-- url     : https://prove2.me/submissions/9bb7646b-e2cc-4366-b4c7-cb1b86516658

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Theorems.Thm_GroundTheory_LocalField_normedField_properSpace

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
theorem _root_.solution :
    letI := (finiteExtensionStructure K L).rel
    letI := (finiteExtensionStructure K L).top
    IsNonarchimedeanLocalField L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  have := normedField_properSpace K
  let := spectralNormedField K L
  have := spectralNormedField_isUltrametricDist K L
  let := (finiteExtensionStructure K L).rel
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => (NormedField.toValued (K := L)).is_topological_valuation s)
  · let : NormedSpace K L := spectralNorm.normedSpace K L
    have : ProperSpace L := FiniteDimensional.proper K L
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance
end GroundTheory.LocalField
