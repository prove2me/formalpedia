-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.exists_ne_aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:51.236798+00:00
-- url     : https://prove2.me/submissions/20cf1d6a-94db-4e3b-92c6-be9b719e4128

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac

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
theorem _root_.solution {f : ℂ → ℂ} (h : ∃ z, f z ≠ 0) (α β γ : ℝ) (hβ : β ≠ 0) :
    ∃ y : ℂ, f (aff α β γ (0, y)) ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  refine ⟨(z - γ) / β, ?_⟩
  have e : aff α β γ (0, (z - γ) / (β : ℂ)) = z := by
    simp only [aff]
    field_simp
    ring
  rwa [e]
end GlobalTheory.CompanionTheory.RgEisGal
