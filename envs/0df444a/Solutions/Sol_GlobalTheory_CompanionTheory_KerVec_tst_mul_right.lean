-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerVec.tst_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:45.803097+00:00
-- url     : https://prove2.me/submissions/379d5bc2-af58-4e6c-ab50-4caa914d75f2

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
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) :=
  ⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩
end GlobalTheory.CompanionTheory.KerVec
