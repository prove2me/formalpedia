-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.ex_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:30.30201+00:00
-- url     : https://prove2.me/submissions/479a7506-88bf-4a01-9747-d9b501ac3ff0

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
theorem _root_.solution (u R : ℝ) :
    ∃ m M : ℝ, m ≤ u ∧ m ≤ -2 * R ∧ (m = u ∨ m = -2 * R) ∧ u ≤ M ∧ R ≤ M ∧ (M = u ∨ M = R) :=
  ⟨min u (-2 * R), max u R, min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _,
    le_max_right _ _, max_choice _ _⟩
end GlobalTheory.CompanionTheory.RgEisGal
