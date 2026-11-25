-- Prove2me | solution 1 for GroundTheory.LocalField.finrank_adjoin_le_of_isEisensteinAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:20.411196+00:00
-- url     : https://prove2.me/submissions/a3e00f25-a914-4bcf-a49f-bd82eb8e02d2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ ≤ f.natDegree := by
  have hint : IsIntegral K α := (isIntegral_of_isEisensteinAt hf hα).tower_top
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hne : f.map (algebraMap 𝒪[K] K) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hinj]
    rintro rfl
    exact hf.leading (by simp)
  rw [IntermediateField.adjoin.finrank hint, ← natDegree_map_eq_of_injective hinj f]
  exact natDegree_le_of_dvd (minpoly.dvd K α (by rw [aeval_map_algebraMap, hα])) hne
end GroundTheory.LocalField
