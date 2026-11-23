-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.aff_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:28.319482+00:00
-- url     : https://prove2.me/submissions/5cd1d105-23dd-4bcc-9e87-aaa6206d5a39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine

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
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring
end GlobalTheory.CompanionTheory.RgEisGal
