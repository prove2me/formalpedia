-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isOpen_orbitPiece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:52.055881+00:00
-- url     : https://prove2.me/submissions/7bc6610a-1f4f-4a86-a760-daf59c63a25b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuousSMul_orbit
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
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {x₀ : X} (hO : IsLocallyClosed (orbit H x₀)) {L : Subgroup H}
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    IsOpen ((Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece L y) := by
  have : LocallyCompactSpace (orbit H x₀) := hO.locallyCompactSpace
  have := continuousSMul_orbit (H := H) x₀
  have hmap := isOpenMap_smul_of_sigmaCompact (G := H) (X := orbit H x₀) ⟨y, hy⟩ _ hLo
  convert hmap using 1
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, Subtype.ext rfl⟩
  · rintro ⟨l, hl, e⟩
    exact ⟨l, hl, congrArg Subtype.val e⟩
end GroundTheory.Automorphic.Whittaker
