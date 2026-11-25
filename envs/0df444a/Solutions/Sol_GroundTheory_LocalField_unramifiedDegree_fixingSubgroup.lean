-- Prove2me | solution 1 for GroundTheory.LocalField.unramifiedDegree_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:55.392811+00:00
-- url     : https://prove2.me/submissions/1832b81a-7fe8-4a88-99cb-6e4a93384b3a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_unramifiedCoord_fixingSubgroup

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
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L.fixingSubgroup) :
    unramifiedDegree K Ω σ = unramifiedDegree L Ω (fixingSubgroupEquiv L σ) ^ residueDegree K L := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, toAdd_pow, map_nsmul, proj_toAdd_unramifiedDegree, nsmul_eq_mul,
    unramifiedCoord_fixingSubgroup]
end GroundTheory.LocalField
