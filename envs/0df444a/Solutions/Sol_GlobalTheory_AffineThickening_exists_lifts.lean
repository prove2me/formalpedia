-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:07:04.950109+00:00
-- url     : https://prove2.me/submissions/0103dcfb-4b30-4115-83ce-10c292fa8656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

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
theorem _root_.solution [IsClosedImmersion i] {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Z, ⊤)) :
    ∃ a, Lifts i U a r :=
  i.app_surjective U hU _
end GlobalTheory.AffineThickening
