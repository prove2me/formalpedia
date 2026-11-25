-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:59.653471+00:00
-- url     : https://prove2.me/submissions/2316143d-479c-405c-bfae-77a119a6df49

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_mul_abs_add
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_norm_cexp_dot

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
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type)
    [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ →
    Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) →
    Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  intro X _ _ T _ _ φ hD hφ
  rw [continuous_iff_continuousAt]
  rintro ⟨l₀, g₀⟩
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hD (l₀.1.re, l₀.2.re) g₀
  have hcont : ∀ g : T, Continuous fun t : ℝ × ℝ => φ t g := fun g =>
    hφ.comp (Continuous.prodMk continuous_id continuous_const)
  have hdot : ∀ t : ℝ × ℝ, Continuous fun l : ℂ × ℂ => Complex.exp (dot l t) := fun t => by
    unfold dot
    fun_prop
  have hdot' : ∀ l : ℂ × ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot l t) := fun l => by
    unfold dot
    have h1 : Continuous fun t : ℝ × ℝ => ((t.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_fst
    have h2 : Continuous fun t : ℝ × ℝ => ((t.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    fun_prop
  have hnear : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀),
      |y.1.1.re - l₀.1.re| ≤ ε ∧ |y.1.2.re - l₀.2.re| ≤ ε ∧ y.2 ∈ U := by
    have c1 : Continuous fun y : (ℂ × ℂ) × T => |y.1.1.re - l₀.1.re| := by fun_prop
    have c2 : Continuous fun y : (ℂ × ℂ) × T => |y.1.2.re - l₀.2.re| := by fun_prop
    have e1 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.1.re - l₀.1.re| < ε :=
      c1.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e2 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.2.re - l₀.2.re| < ε :=
      c2.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e3 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), y.2 ∈ U :=
      continuous_snd.continuousAt.eventually (p := (· ∈ U)) hU
    filter_upwards [e1, e2, e3] with y a b c using ⟨a.le, b.le, c⟩
  have key : ContinuousAt (fun y : (ℂ × ℂ) × T =>
      ∫ t : ℝ × ℝ, Complex.exp (dot y.1 t) • φ t y.2) (l₀, g₀) := by
    refine continuousAt_of_dominated (bound := fun t => M * Real.exp (-ε * (|t.1| + |t.2|)))
      (Eventually.of_forall fun y => ((hdot' y.1).smul (hcont y.2)).aestronglyMeasurable)
      ?_ (integrable_exp_neg_mul_abs_add hε M)
      (Eventually.of_forall fun t => ?_)
    · filter_upwards [hnear] with y hy
      refine Eventually.of_forall fun t => ?_
      have hb := hM (y.1.1.re, y.1.2.re) hy.1 hy.2.1 y.2 hy.2.2 t
      rw [norm_smul, norm_cexp_dot]
      have hp := Real.exp_pos (rdot (y.1.1.re, y.1.2.re) t)
      calc Real.exp (rdot (y.1.1.re, y.1.2.re) t) * ‖φ t y.2‖
          ≤ Real.exp (rdot (y.1.1.re, y.1.2.re) t) *
            (M * Real.exp (-rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) := by
            gcongr
        _ = M * (Real.exp (rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-rdot (y.1.1.re, y.1.2.re) t)) *
            Real.exp (-ε * (|t.1| + |t.2|)) := by ring
        _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    · have h1 : Continuous fun y : (ℂ × ℂ) × T => Complex.exp (dot y.1 t) :=
        (hdot t).comp continuous_fst
      have h2 : Continuous fun y : (ℂ × ℂ) × T => φ t y.2 :=
        hφ.comp (Continuous.prodMk continuous_const continuous_snd)
      exact (h1.smul h2).continuousAt
  exact continuousAt_const.smul key
end GlobalTheory.CompanionTheory.TubeFourier
