-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.smul_orbitPiece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:37.677671+00:00
-- url     : https://prove2.me/submissions/b4757338-2cc5-4970-b660-848673f996b9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {A : Subgroup H} {j : H} (hj : ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    (hj' : ∀ a ∈ A, j⁻¹ * a * j ∈ A) (y : X) : j • orbitPiece A y = orbitPiece A (j • y) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨j * a * j⁻¹, hj a ha, ?_⟩
    simp [mul_smul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(j⁻¹ * a * j) • y, ⟨j⁻¹ * a * j, hj' a ha, rfl⟩, ?_⟩
    simp [mul_smul]
end GroundTheory.Automorphic.Whittaker
