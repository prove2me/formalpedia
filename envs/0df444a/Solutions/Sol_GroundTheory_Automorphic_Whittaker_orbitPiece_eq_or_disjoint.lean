-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.orbitPiece_eq_or_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:05.039801+00:00
-- url     : https://prove2.me/submissions/3e8761e0-24c4-4a96-bd54-e68a154743d4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_eq_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (L : Subgroup H) (y z : X) :
    orbitPiece L y = orbitPiece L z ∨ Disjoint (orbitPiece L y) (orbitPiece L z) := by
  by_cases h : Disjoint (orbitPiece L y) (orbitPiece L z)
  · exact Or.inr h
  · obtain ⟨x, hxy, hxz⟩ := Set.not_disjoint_iff.1 h
    exact Or.inl ((orbitPiece_eq_of_mem hxy).symm.trans (orbitPiece_eq_of_mem hxz))
end GroundTheory.Automorphic.Whittaker
