-- Prove2me | solution 1 for GroundTheory.Automorphic.isClosedEmbedding_coe_unitaryPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:19.433471+00:00
-- url     : https://prove2.me/submissions/b3c61b3c-d499-4d90-a612-c6c33ed8438d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Theorems.Thm_GroundTheory_Automorphic_t2Space_tensor
import Theorems.Thm_GroundTheory_Automorphic_range_coe_unitaryPoints

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
    IsClosedEmbedding (fun g : unitaryPoints K E H R => (unitaryMat g)) := by
  have : T2Space (R ⊗[K] E) := t2Space_tensor R
  refine ⟨isEmbedding_coe_unitaryPoints H R hH, ?_⟩
  rw [range_coe_unitaryPoints H R hH]
  exact isClosed_eq
    (((continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul continuous_id) continuous_const
end GroundTheory.Automorphic
