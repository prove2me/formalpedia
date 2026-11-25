-- Prove2me | solution 1 for GroundTheory.LocalField.adjoin_eq_top_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:29.639905+00:00
-- url     : https://prove2.me/submissions/b0caf1c1-f079-4cb3-b8b0-a8dbdb25d4f7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_minpoly_isEisensteinAt_of_irreducible
import Theorems.Thm_GroundTheory_LocalField_minpoly_eq_map_of_irreducible

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
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ
namespace GroundTheory.LocalField
theorem _root_.solution : K⟮(ϖ : L)⟯ = ⊤ := by
  have hint : IsIntegral K (ϖ : L) := ((isIntegral_iff K L _).mpr ϖ.2).tower_top
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, minpoly_eq_map_of_irreducible h hϖ,
    (minpoly.monic ((isIntegral_iff K L _).mpr ϖ.2)).natDegree_map]
  exact (minpoly_isEisensteinAt_of_irreducible h hϖ).2
end GroundTheory.LocalField
