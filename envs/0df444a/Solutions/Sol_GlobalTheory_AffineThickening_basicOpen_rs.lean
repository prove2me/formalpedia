-- Prove2me | solution 1 for GlobalTheory.AffineThickening.basicOpen_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:08.460666+00:00
-- url     : https://prove2.me/submissions/b3aa3058-3cf8-4a3e-8c4c-6adf94474daa

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
namespace GlobalTheory.AffineThickening
theorem _root_.solution {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    Y.basicOpen (rs h a) = V ⊓ Y.basicOpen a :=
  Y.basicOpen_res a (homOfLE h).op
end GlobalTheory.AffineThickening
