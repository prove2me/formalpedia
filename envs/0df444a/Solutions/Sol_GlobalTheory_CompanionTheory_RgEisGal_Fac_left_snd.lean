-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_left_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:52.639007+00:00
-- url     : https://prove2.me/submissions/ae2b1586-7055-40a6-a5f3-fd7f550cd24d

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
    (h : ∀ x ∈ Ω, x.2 < a) : Fac (fun l => f l.2) Ω := by
  have := Fac_left hf 0 1 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this
end GlobalTheory.CompanionTheory.RgEisGal
