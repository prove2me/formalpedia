-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.gaussTube_of_tubeGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:48.083426+00:00
-- url     : https://prove2.me/submissions/670deb03-3b07-4776-a696-4aa6eb9ebf89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_gauss_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω where
  hol p v := by
    have h1 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).1 ^ 2 + (p + τ • v).2 ^ 2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      fun_prop
    exact h1.differentiableOn.smul (h.hol g p v)
  cont := by
    have h1 : ContinuousOn (fun l : ℂ × ℂ => F l g) (tube Ω) :=
      h.cont.comp (f := fun l : ℂ × ℂ => (l, g)) (by fun_prop) fun l hl => ⟨hl, trivial⟩
    exact ContinuousOn.smul (by fun_prop) h1
  decay C hC hc := by
    obtain ⟨U, hU, M, hM⟩ := gauss_bound h hC hc g
    exact ⟨M, fun l hl => hM g (mem_of_mem_nhds hU) l hl⟩
end GlobalTheory.CompanionTheory.TubeFourier
