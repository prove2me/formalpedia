-- Prove2me | solution 1 for GlobalTheory.AffineThickening.eq_of_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:52.165571+00:00
-- url     : https://prove2.me/submissions/921d69c8-e710-484f-9429-fbcf2aabc2cd

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
theorem _root_.solution [Surjective i] {U V : Y.Opens} (h : i ⁻¹ᵁ U = i ⁻¹ᵁ V) : U = V := by
  ext y
  obtain ⟨z, rfl⟩ := i.surjective y
  exact SetLike.ext_iff.1 h z
end GlobalTheory.AffineThickening
