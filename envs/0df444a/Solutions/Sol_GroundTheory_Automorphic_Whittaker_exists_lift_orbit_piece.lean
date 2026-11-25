-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_lift_orbit_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:24.029267+00:00
-- url     : https://prove2.me/submissions/4136d9cf-9a5d-401d-aaa0-ed6325b1a917

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_subset_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_indicator


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
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ f ∈ supportedIn U, ∀ x ∈ orbit H x₀, f x = (orbitPiece L y).indicator 1 x := by
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  exact exists_lift_indicator hU (hO ▸ inter_subset_left) (orbitPiece_subset_orbit hy)
    (isCompact_orbitPiece hLc y) (isOpen_orbitPiece hOl hLo hy)
end GroundTheory.Automorphic.Whittaker
