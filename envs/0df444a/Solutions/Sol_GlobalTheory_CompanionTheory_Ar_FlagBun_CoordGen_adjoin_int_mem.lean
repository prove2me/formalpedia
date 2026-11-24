-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.adjoin_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:24.016599+00:00
-- url     : https://prove2.me/submissions/4427bc04-f67a-4ab9-ad00-2bb6154462d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution {K : Type*} [Field K] (L : Subfield K) {t : Set K} (ht : ∀ a ∈ t, a ∈ L) {g : K}
    (hg : g ∈ Algebra.adjoin ℤ t) : g ∈ L := by
  induction hg using Algebra.adjoin_induction with
  | mem a ha => exact ht a ha
  | algebraMap n => simpa using intCast_mem L n
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
