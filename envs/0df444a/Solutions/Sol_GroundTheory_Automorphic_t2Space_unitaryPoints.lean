-- Prove2me | solution 1 for GroundTheory.Automorphic.t2Space_unitaryPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:22.362714+00:00
-- url     : https://prove2.me/submissions/0afe637c-1e69-4fba-959b-49380f78fe4d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology

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
    T2Space (unitaryPoints K E H R) :=
  (isEmbedding_unitaryCoords H R (Module.finBasis K E) hH).t2Space
end GroundTheory.Automorphic
