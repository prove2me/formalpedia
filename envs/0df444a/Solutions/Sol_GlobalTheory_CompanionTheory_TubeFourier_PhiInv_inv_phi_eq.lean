-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:16.646019+00:00
-- url     : https://prove2.me/submissions/a11872af-67cb-4053-959f-59f94cb62d76

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_dot_pt_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_integrable_gaussian_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_hat_eq_smul
import Theorems.Thm_GlobalTheory_T_exponential_fourier_integral_bound
import Theorems.Thm_GlobalTheory_T_fourier_inversion_real_plane


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.PhiInv
namespace GlobalTheory.CompanionTheory.TubeFourier.PhiInv
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X)
    (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) →
    (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    Continuous (phi G x) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ,
      ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) →
    ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  intro X _ _ _ G x hc ⟨M, hM⟩ hphic ⟨ε, hε, M', hM'⟩ y
  have hint : Integrable (fun y : ℝ × ℝ => G (pt x y)) :=
    Integrable.mono' (integrable_gaussian_prod.const_mul M) hc.aestronglyMeasurable
      (Eventually.of_forall fun y => hM y)
  have hdx : ∀ t, dot (pt x 0) t = ((rdot x t : ℝ) : ℂ) := by
    intro t; rw [dot_pt_eq]; simp [rdot]
  have hl : ((pt x 0).1.re, (pt x 0).2.re) = x := by simp [pt]
  have hint2 : Integrable (fun t : ℝ × ℝ =>
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) := by
    have h0 := (GlobalTheory.T.exponential_fourier_integral_bound X (phi G x) (pt x 0) ε M' hε hphic (by rw [hl]; exact hM')).1
    refine h0.congr (Eventually.of_forall fun t => ?_)
    show Complex.exp (dot (pt x 0) t) • phi G x t =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)
    rw [hdx, hat_eq_smul]
  have key := GlobalTheory.T.fourier_inversion_real_plane X (fun y => G (pt x y)) hc hint hint2 y
  rw [key]
  unfold inv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [hat_eq_smul, smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring
end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
