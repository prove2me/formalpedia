-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:33.421123+00:00
-- url     : https://prove2.me/submissions/38b8a788-3498-4c35-be87-2f26c3dfc292

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_mul
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {α : Type*} [TopologicalSpace α]
namespace GroundTheory.Automorphic.ContragredientTranspose
namespace ContCoeff
theorem _root_.solution {ι : Type*} (s : Finset ι) {P : ι → α → F[X]}
    (hP : ∀ i ∈ s, ContCoeff (P i)) : ContCoeff fun a => ∏ i ∈ s, P i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ContCoeff.const (α := α) (1 : F[X])
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hP j (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))
end ContCoeff
end GroundTheory.Automorphic.ContragredientTranspose
