-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:35.918046+00:00
-- url     : https://prove2.me/submissions/b777fc72-0ad6-4a69-8182-2dbf956714ec

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {A : ℂ × ℂ → X} {Ω Ω' : Set (ℝ × ℝ)} (hA : Fac A Ω) (h : Ω' ⊆ Ω) : Fac A Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  exact ⟨fun p v => (hA.hol p v).mono fun τ hτ => ht hτ, hA.cont.mono ht,
    fun C hC => hA.bdd C (hC.trans h)⟩
end GlobalTheory.CompanionTheory.RgEisGal
