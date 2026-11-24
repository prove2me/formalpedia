-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:37.884878+00:00
-- url     : https://prove2.me/submissions/e62c0cd2-28cd-41c6-b7a4-dd60491d5667

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om2
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_open_convex2

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
theorem _root_.solution (N r : ℝ) : IsOpen (Om2 N r) ∧ Convex ℝ (Om2 N r) :=
  open_convex2 (-1) (-1) N 0 1 1 r fun x => by
    rw [mem_Om2]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
end GlobalTheory.CompanionTheory.RgEisGal
