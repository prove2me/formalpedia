-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.shiftFst_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:53.298941+00:00
-- url     : https://prove2.me/submissions/f2b8849c-b5db-4268-8ff9-2f881bc3818b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_shiftFst_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_sq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring
end GlobalTheory.CompanionTheory.TubeFourier
