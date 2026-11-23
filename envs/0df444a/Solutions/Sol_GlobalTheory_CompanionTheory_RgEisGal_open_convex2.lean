-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.open_convex2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:19.265161+00:00
-- url     : https://prove2.me/submissions/2458ebec-15c3-495f-9434-6f2e126d96f3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_hp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_convex_hp

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
theorem _root_.solution {Ω : Set (ℝ × ℝ)} (α₁ β₁ γ₁ α₂ β₂ γ₂ r : ℝ)
    (h : ∀ x, x ∈ Ω ↔ r < affR α₁ β₁ γ₁ x ∧ r < affR α₂ β₂ γ₂ x) : IsOpen Ω ∧ Convex ℝ Ω := by
  have e : Ω = {x | r < affR α₁ β₁ γ₁ x} ∩ {x | r < affR α₂ β₂ γ₂ x} := by
    ext x; exact h x
  rw [e]
  exact ⟨(isOpen_hp _ _ _ _).inter (isOpen_hp _ _ _ _), (convex_hp _ _ _ _).inter (convex_hp _ _ _ _)⟩
end GlobalTheory.CompanionTheory.RgEisGal
