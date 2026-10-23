-- Prove2me | solution 2 for JHolomorphic.exists_holomorphic_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:50:25.387111+00:00
-- url     : https://prove2.me/submissions/2ae38c3d-3830-4210-865a-4f14305cfbbd

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_exists_local_complex_frame
import Theorems.Thm_JHolomorphic_exists_similarity_of_norm_dbar_le
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Theorem 2.26, for a complex structure varying with the point. -/
theorem exists_holomorphic_factorization_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z) ∧
          ∀ w, Φ z (Complex.I • w) = Jbar z (Φ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Φ z (f z) := by
  obtain ⟨ρ, hρ, hρ1, Ψ, Ψi, hΨ, hΨi, hprop⟩ := exists_local_complex_frame n hn Jbar hJbar hJbar2
  have hρ1' : ball (0 : ℂ) ρ ⊆ ball 0 1 := ball_subset_ball hρ1
  have hK : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ := closedBall_subset_ball (by linarith)
  have hKc : IsCompact (closedBall (0 : ℂ) (ρ / 2)) := isCompact_closedBall _ _
  let g : ℂ → EuclideanSpace ℂ (Fin n) := fun z => Ψi z (h z)
  have hgd : ContDiffOn ℝ ∞ g (ball 0 ρ) := hΨi.clm_apply (hh.mono hρ1')
  -- bounds on the compact disc
  have hDΨi : ContinuousOn (fderiv ℝ Ψi) (ball 0 ρ) :=
    hΨi.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨CD1, hCD1⟩ := hKc.exists_bound_of_continuousOn
    ((hDΨi.clm_apply (continuousOn_const (c := (1 : ℂ)))).mono hK)
  obtain ⟨CDI, hCDI⟩ := hKc.exists_bound_of_continuousOn
    ((hDΨi.clm_apply (continuousOn_const (c := Complex.I))).mono hK)
  set CD := max CD1 CDI with hCD_def
  obtain ⟨Ci, hCi⟩ := hKc.exists_bound_of_continuousOn (hΨi.continuousOn.mono hK)
  obtain ⟨CA, hCA⟩ := hKc.exists_bound_of_continuousOn (hA.continuousOn.mono (hK.trans hρ1'))
  obtain ⟨CΨ, hCΨ⟩ := hKc.exists_bound_of_continuousOn (hΨ.continuousOn.mono hK)
  have hM : ∀ z ∈ ball (0 : ℂ) (ρ / 2),
      ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤
        ((CD + CD + Ci * CA) * CΨ) * ‖g z‖ := by
    intro z hz
    have hzK : z ∈ closedBall (0 : ℂ) (ρ / 2) := ball_subset_closedBall hz
    have hzρ : z ∈ ball (0 : ℂ) ρ := hK hzK
    have hz1 : z ∈ ball (0 : ℂ) 1 := hρ1' hzρ
    have hΨid := hΨi.differentiableOn (by simp) z hzρ |>.differentiableAt (isOpen_ball.mem_nhds hzρ)
    have hhd := hh.differentiableOn (by simp) z hz1 |>.differentiableAt (isOpen_ball.mem_nhds hz1)
    have hfd : ∀ v, fderiv ℝ g z v = Ψi z (fderiv ℝ h z v) + fderiv ℝ Ψi z v (h z) := by
      intro v
      rw [show g = fun y => Ψi y (h y) from rfl, fderiv_clm_apply hΨid hhd]
      simp
    obtain ⟨hl, hr, hI⟩ := hprop z hzρ
    have hJ : ∀ x, Complex.I • Ψi z x = Ψi z (Jbar z x) := by
      intro x
      have := hI (Ψi z x)
      rw [hr] at this
      rw [← this, hl]
    have hsum : fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I =
        fderiv ℝ Ψi z 1 (h z) + Complex.I • fderiv ℝ Ψi z Complex.I (h z) - Ψi z (A z (h z)) := by
      rw [hfd, hfd, smul_add, hJ]
      have := heq z hz1
      have h2 : fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) = -A z (h z) :=
        eq_neg_of_add_eq_zero_left this
      have h3 : Ψi z (fderiv ℝ h z 1) + Ψi z (Jbar z (fderiv ℝ h z Complex.I)) =
          -Ψi z (A z (h z)) := by rw [← map_add, h2, map_neg]
      rw [sub_eq_add_neg, ← h3]
      abel
    have hhz : h z = Ψ z (g z) := (hr (h z)).symm
    have hnh : ‖h z‖ ≤ CΨ * ‖g z‖ := by
      rw [hhz]; exact (Ψ z).le_of_opNorm_le (hCΨ z hzK) _
    have hCD0 : 0 ≤ CD := (norm_nonneg _).trans ((hCD1 z hzK).trans (le_max_left _ _))
    have hCi0 : 0 ≤ Ci := (norm_nonneg _).trans (hCi z hzK)
    have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hCA z hzK)
    have e1 : ‖fderiv ℝ Ψi z 1 (h z)‖ ≤ CD * ‖h z‖ :=
      (fderiv ℝ Ψi z 1).le_of_opNorm_le ((hCD1 z hzK).trans (le_max_left _ _)) _
    have e2 : ‖Complex.I • fderiv ℝ Ψi z Complex.I (h z)‖ ≤ CD * ‖h z‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact (fderiv ℝ Ψi z Complex.I).le_of_opNorm_le ((hCDI z hzK).trans (le_max_right _ _)) _
    have e3 : ‖Ψi z (A z (h z))‖ ≤ Ci * CA * ‖h z‖ := by
      refine ((Ψi z).le_opNorm _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul (hCi z hzK) ((A z).le_of_opNorm_le (hCA z hzK) _) (norm_nonneg _) hCi0
    rw [hsum]
    calc _ ≤ ‖fderiv ℝ Ψi z 1 (h z) + Complex.I • fderiv ℝ Ψi z Complex.I (h z)‖ +
          ‖Ψi z (A z (h z))‖ := norm_sub_le _ _
      _ ≤ CD * ‖h z‖ + CD * ‖h z‖ + Ci * CA * ‖h z‖ := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add e1 e2)
      _ = (CD + CD + Ci * CA) * ‖h z‖ := by ring
      _ ≤ (CD + CD + Ci * CA) * (CΨ * ‖g z‖) := by
          gcongr
      _ = _ := by ring
  obtain ⟨ε, hε, Φ₀, f, hΦc, hΦb, hf, hgf⟩ :=
    exists_similarity_of_norm_dbar_le n (ρ / 2) _ (by linarith) g
      ((hgd.mono (ball_subset_ball (by linarith))).of_le (by simp)) hM
  have hε' : 0 < min ε (ρ / 4) := lt_min hε (by linarith)
  have hs1 : closedBall (0 : ℂ) (min ε (ρ / 4)) ⊆ closedBall 0 ε :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hs2 : closedBall (0 : ℂ) (min ε (ρ / 4)) ⊆ ball 0 ρ :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  refine ⟨min ε (ρ / 4), hε', fun z => (Ψ z).comp ((Φ₀ z).restrictScalars ℝ), f, ?_, ?_,
    hf.mono (ball_subset_ball (min_le_left _ _)), ?_⟩
  · exact (hΨ.continuousOn.mono hs2).clm_comp
      ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn (hΦc.mono hs1))
  · intro z hz
    obtain ⟨hl, hr, hI⟩ := hprop z (hs2 hz)
    refine ⟨?_, fun w => ?_⟩
    · exact (Function.bijective_iff_has_inverse.2 ⟨Ψi z, hl, hr⟩).comp (hΦb z (hs1 hz))
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
        map_smul, hI]
  · intro z hz
    have hz' : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left _ _) hz
    obtain ⟨hl, hr, hI⟩ := hprop z (hs2 (ball_subset_closedBall hz))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← hgf z hz', hr]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z) ∧
          ∀ w, Φ z (Complex.I • w) = Jbar z (Φ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Φ z (f z) :=
  exists_holomorphic_factorization_aux n hn Jbar A hJbar hJbar2 hA h hh heq
