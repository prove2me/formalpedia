-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_strip_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:09.692276+00:00
-- url     : https://prove2.me/submissions/646ee121-2eca-4816-9629-4fe5ed05a3a9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_strip


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
theorem _root_.solution {f : ℂ → X} (hf : StripEntire f) (Ω : Set (ℝ × ℝ)) : Fac (fun l => f l.2) Ω := by
  have := Fac_strip hf 0 1 0 Ω
  simpa [aff] using this
end GlobalTheory.CompanionTheory.RgEisGal
