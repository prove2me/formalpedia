-- Prove2me | solution 1 for GlobalTheory.JR.WeilMix.isOpen_setOf_eq_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:09.751698+00:00
-- url     : https://prove2.me/submissions/6ab9e506-d75e-45ad-a409-96c9b37179ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix
namespace GlobalTheory.JR.WeilMix
theorem _root_.solution {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg p,
    (IsLocallyConstant.iff_eventually_eq h).1 hh p] with q h1 h2
  show g q = h q
  rw [h1, h2]; exact hp
end GlobalTheory.JR.WeilMix
