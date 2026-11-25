-- Prove2me | solution 1 for GroundTheory.LocalField.exists_sub_algebraMap_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:16.629502+00:00
-- url     : https://prove2.me/submissions/82ce0dd1-06ef-427f-ad12-de9bde23e4da

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank


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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (h : residueDegree K L = 1) (w : 𝒪[L]) :
    ∃ c : 𝒪[K], w - algebraMap 𝒪[K] 𝒪[L] c ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
  rw [residueDegree_eq_finrank, finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero] at h
  obtain ⟨c, hc⟩ := h (IsLocalRing.residue 𝒪[L] w)
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨c', ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, Algebra.smul_def, mul_one,
    IsLocalRing.ResidueField.algebraMap_residue, sub_self]
end GroundTheory.LocalField
