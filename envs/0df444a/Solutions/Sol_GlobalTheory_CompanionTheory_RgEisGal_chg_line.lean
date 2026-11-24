-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.chg_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:23.558002+00:00
-- url     : https://prove2.me/submissions/df865380-71ca-44f7-a72f-a1c9354d7a33

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_aff_line

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
theorem _root_.solution (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl
end GlobalTheory.CompanionTheory.RgEisGal
