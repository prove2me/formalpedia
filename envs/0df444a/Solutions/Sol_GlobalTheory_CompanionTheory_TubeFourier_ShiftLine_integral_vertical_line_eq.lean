-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.integral_vertical_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:41:33.336008+00:00
-- url     : https://prove2.me/submissions/43e01f3e-617e-4e0b-b376-5a0523233a49

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
namespace GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
theorem _root_.solution {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ) (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b})
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) :
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  have hpt : ∀ c y : ℝ, (⟨c, y⟩ : ℂ) = (c : ℂ) + (y : ℂ) * Complex.I := by
    intro c y
    apply Complex.ext <;> simp
  simp only [hpt]
  have hint : ∀ c ∈ Set.Icc a b,
      Integrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I)) := by
    intro c hc
    have hcont : Continuous fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I) :=
      hd.continuousOn.comp_continuous (by fun_prop) (fun y => by simpa using hc)
    refine ((integrable_exp_neg_mul_sq one_pos).const_mul M).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have := hb ((c : ℂ) + (y : ℂ) * Complex.I) (by simpa using hc)
    simpa using this
  have hhor : ∀ s : ℝ,
      ‖∫ x in a..b, f ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M * Real.exp (-s ^ 2) * (b - a) := by
    intro s
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := M * Real.exp (-s ^ 2)) (f := fun x : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I)) ?_
    · rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    · intro x hx
      rw [Set.uIoc_of_le hab] at hx
      have := hb ((x : ℂ) + (s : ℂ) * Complex.I) (by simp; exact ⟨hx.1.le, hx.2⟩)
      simpa using this
  have hrect : ∀ R : ℝ, 0 ≤ R →
      ((∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
          ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) +
        Complex.I • (∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • (∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro R _
    refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -R⟩ ⟨b, R⟩ ?_
    refine hd.mono fun z hz => ?_
    exact (Set.uIcc_of_le hab).subset (Complex.mem_reProdIm.mp hz).1
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have hH : Tendsto (fun R : ℝ => (∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
      ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) atTop (𝓝 0) := by
    have hT : Tendsto (fun R : ℝ => 2 * (M * Real.exp (-R ^ 2) * (b - a))) atTop (𝓝 0) := by
      simpa using ((hexp.const_mul M).mul_const (b - a)).const_mul 2
    refine squeeze_zero_norm (fun R => ?_) hT
    calc _ ≤ ‖∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ +
            ‖∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ M * Real.exp (-(-R) ^ 2) * (b - a) + M * Real.exp (-R ^ 2) * (b - a) :=
          add_le_add (hhor (-R)) (hhor R)
      _ = 2 * (M * Real.exp (-R ^ 2) * (b - a)) := by
          rw [neg_sq]
          ring
  have hVa : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩) tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩) tendsto_neg_atTop_atBot tendsto_id
  have hlim := (hH.add (hVb.const_smul Complex.I)).sub (hVa.const_smul Complex.I)
  have heq : (0 : Y) + Complex.I • (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr'
      ((eventually_ge_atTop 0).mono fun R hR => (hrect R hR).symm))
  rw [zero_add, ← smul_sub, smul_eq_zero] at heq
  rcases heq with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.mp h).symm
end GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
