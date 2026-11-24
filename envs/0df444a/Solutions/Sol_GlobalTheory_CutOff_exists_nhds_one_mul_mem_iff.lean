-- Prove2me | solution 1 for GlobalTheory.CutOff.exists_nhds_one_mul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:38.153389+00:00
-- url     : https://prove2.me/submissions/816b7447-873d-4902-b751-e3ed0bd2fb20

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff
namespace GlobalTheory.CutOff
theorem _root_.solution {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_left hUk hUo subset_rfl
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩
  rintro w ⟨hw, hw'⟩ x
  constructor
  · intro h
    have : w⁻¹ * (w * x) ∈ U := hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)
    simpa using this
  · intro h
    exact hVU (Set.mul_mem_mul hw h)
end GlobalTheory.CutOff
