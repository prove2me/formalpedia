-- Prove2me | solution 1 for GlobalTheory.AffineThickening.rs_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:14.37745+00:00
-- url     : https://prove2.me/submissions/6b7a22b2-be40-422f-ade6-c7d314104952

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
theorem _root_.solution {Y : Scheme.{u}} {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(Y, U)) :
    rs h' (rs h a) = rs (h'.trans h) a := by
  simp only [rs, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end GlobalTheory.AffineThickening
