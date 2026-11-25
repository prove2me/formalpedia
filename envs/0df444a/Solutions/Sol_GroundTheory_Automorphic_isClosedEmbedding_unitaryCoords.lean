-- Prove2me | solution 1 for GroundTheory.Automorphic.isClosedEmbedding_unitaryCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:40.917639+00:00
-- url     : https://prove2.me/submissions/81eed1a6-8e10-41b9-b162-a9d1938ef43b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Theorems.Thm_GroundTheory_Automorphic_isClosedEmbedding_coe_unitaryPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] tensorTopology finite_of_isQuadraticExtension
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
attribute [local instance] isModuleTopology_tensor
attribute [local instance] isTopologicalRing_tensor
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {H R}
variable (H R)
namespace GroundTheory.Automorphic
theorem _root_.solution (hH : IsUnit H.det) [T2Space R] :
    IsClosedEmbedding (unitaryCoords H R b) :=
  (matrixCoordsHomeomorph R b).isClosedEmbedding.comp (isClosedEmbedding_coe_unitaryPoints H R hH)
end GroundTheory.Automorphic
