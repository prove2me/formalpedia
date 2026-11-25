-- Prove2me | solution 1 for GroundTheory.Automorphic.range_coe_unitaryPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:21.891374+00:00
-- url     : https://prove2.me/submissions/5e42a277-a24c-41e2-9198-945016c48112

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_unitaryGroupMatrix_iff


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
theorem _root_.solution (hH : IsUnit H.det) :
    Set.range (fun g : unitaryPoints K E H R => (unitaryMat g)) =
      {M | (M.map (conjBase K E R))ᵀ * baseMatrix K H R * M = baseMatrix K H R} := by
  ext M
  have := exists_mem_unitaryGroupMatrix_iff (conjBase K E R) (isUnit_det_baseMatrix (K := K) H R hH) M
  constructor
  · rintro ⟨g, rfl⟩
    exact this.1 ⟨g, g.2, rfl⟩
  · intro hM
    obtain ⟨g, hg, rfl⟩ := this.2 hM
    exact ⟨⟨g, hg⟩, rfl⟩
end GroundTheory.Automorphic
