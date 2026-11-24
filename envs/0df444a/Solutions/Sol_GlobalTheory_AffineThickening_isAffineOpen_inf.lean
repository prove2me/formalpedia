-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isAffineOpen_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:02.263507+00:00
-- url     : https://prove2.me/submissions/ab428466-1b20-4f0c-92c9-abb1cedc87a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_basicOpen_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
namespace GlobalTheory.AffineThickening
theorem _root_.solution [IsClosedImmersion i] [Surjective i] {U D : Y.Opens}
    (hU : IsAffineOpen U) {r : Γ(Z, ⊤)} (hD : i ⁻¹ᵁ D = Z.basicOpen r) :
    IsAffineOpen (U ⊓ D) := by
  obtain ⟨a, ha⟩ := exists_lifts (i := i) hU r
  rw [ha.basicOpen_eq hD]
  exact hU.basicOpen a
end GlobalTheory.AffineThickening
