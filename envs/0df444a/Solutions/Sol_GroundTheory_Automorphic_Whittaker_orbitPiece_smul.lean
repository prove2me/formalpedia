-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.orbitPiece_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:05.778984+00:00
-- url     : https://prove2.me/submissions/65e6303b-d62d-4ba9-b9f4-306831eb7f0e

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
theorem _root_.solution (L : Subgroup H) (h : H) (y : X) :
    orbitPiece L (h • y) = h • orbitPiece (L.map (MulAut.conj h⁻¹).toMonoidHom) y := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨(h⁻¹ * l * h) • y, ⟨h⁻¹ * l * h, ⟨l, hl, by simp⟩, rfl⟩, ?_⟩
    simp [mul_smul]
  · rintro ⟨_, ⟨_, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩
    refine ⟨l, hl, ?_⟩
    simp [mul_smul]
end GroundTheory.Automorphic.Whittaker
