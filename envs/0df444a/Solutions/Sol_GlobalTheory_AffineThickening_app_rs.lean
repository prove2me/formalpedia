-- Prove2me | solution 1 for GlobalTheory.AffineThickening.app_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:18.087459+00:00
-- url     : https://prove2.me/submissions/17b4d614-3835-4676-9566-049f47fa9f23

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
namespace GlobalTheory.AffineThickening
theorem _root_.solution {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (i.app V).hom (rs h a) = rs (i.preimage_mono h) ((i.app U).hom a) := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  exact this
end GlobalTheory.AffineThickening
