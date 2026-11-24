-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_left_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:52.609864+00:00
-- url     : https://prove2.me/submissions/822dba36-defe-4b38-8300-02f671d8eecc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.1 < a) : Fac (fun l => f l.1) Ω := by
  have := Fac_left hf 1 0 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this
end GlobalTheory.CompanionTheory.RgEisGal
