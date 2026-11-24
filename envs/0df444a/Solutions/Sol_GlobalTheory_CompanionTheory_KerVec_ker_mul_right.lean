-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerVec.ker_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:44.878052+00:00
-- url     : https://prove2.me/submissions/350bc30a-24a2-4ed3-8e54-a8a5b8e8f1a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousAtOfSqBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerVec
namespace GlobalTheory.CompanionTheory.KerVec
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) (φ : G → ℂ) (z y w : G) :
    ker Γ (fun g => φ (g * w)) z y = ker Γ φ z (y * w) := by
  simp only [ker, mul_assoc]
end GlobalTheory.CompanionTheory.KerVec
