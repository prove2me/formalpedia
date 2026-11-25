-- Prove2me | solution 1 for GroundTheory.Automorphic.locallyCompactSpace_unitaryPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:29.708807+00:00
-- url     : https://prove2.me/submissions/d482a545-6272-4f2d-be7b-53330e00e19f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Theorems.Thm_GroundTheory_Automorphic_isClosedEmbedding_unitaryCoords

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
theorem _root_.solution (hH : IsUnit H.det) [T2Space R]
    [LocallyCompactSpace R] : LocallyCompactSpace (unitaryPoints K E H R) :=
  (isClosedEmbedding_unitaryCoords H R (Module.finBasis K E) hH).locallyCompactSpace
end GroundTheory.Automorphic
