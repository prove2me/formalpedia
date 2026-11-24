-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.TubeGood_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:35.451264+00:00
-- url     : https://prove2.me/submissions/1755a68c-0838-4fa2-abc6-b88ecc03164a

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
theorem _root_.solution {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ
end GlobalTheory.CompanionTheory.RgEisGal
