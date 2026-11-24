-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:27.688009+00:00
-- url     : https://prove2.me/submissions/6c7b84a5-335d-4e50-8dc8-9ca56206503a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_preimage_basicOpen
import Theorems.Thm_GlobalTheory_AffineThickening_eq_of_preimage_eq

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
namespace Lifts
theorem _root_.solution [Surjective i] {U D : Y.Opens} {a : Γ(Y, U)} {r : Γ(Z, ⊤)}
    (ha : Lifts i U a r) (hD : i ⁻¹ᵁ D = Z.basicOpen r) : U ⊓ D = Y.basicOpen a := by
  apply eq_of_preimage_eq (i := i)
  rw [ha.preimage_basicOpen, Scheme.Hom.preimage_inf, hD]
end Lifts
end GlobalTheory.AffineThickening
