-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:14.368379+00:00
-- url     : https://prove2.me/submissions/d49d3850-64ac-45f3-b07a-a3877d0026ed

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_smul

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
theorem _root_.solution {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'
end GlobalTheory.CompanionTheory.RgEisGal
