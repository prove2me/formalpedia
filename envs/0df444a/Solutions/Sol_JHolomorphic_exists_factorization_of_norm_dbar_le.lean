-- Prove2me | solution 1 for JHolomorphic.exists_factorization_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T20:52:30.109332+00:00
-- url     : https://prove2.me/submissions/f04de498-08df-42f5-8cfc-ab010aeb7aaa

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_exists_local_complex_frame
import Theorems.Thm_JHolomorphic_exists_similarity_of_norm_dbar_le
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff

/-- The unit-disc case. -/
theorem c1k_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖) :
    ∃ ε > (0 : ℝ), ε < 1 ∧ ∃ Θ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Θ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Θ z) ∧
          ∀ w, Θ z (Complex.I • w) = Jbar z (Θ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Θ z (f z) := by
  obtain ⟨ρf, hρf, hρf1, Ψ, Ψi, hΨ, hΨi, hprop⟩ := exists_local_complex_frame n hn Jbar hJbar hJbar2
  have hρ1' : ball (0 : ℂ) ρf ⊆ ball 0 1 := ball_subset_ball hρf1
  set σ := ρf / 2 with hσ_def
  have hσ : 0 < σ := by linarith
  have hK : closedBall (0 : ℂ) σ ⊆ ball 0 ρf := closedBall_subset_ball (by linarith)
  have hKc : IsCompact (closedBall (0 : ℂ) σ) := isCompact_closedBall _ _
  set M' := max M 0
  let g : ℂ → EuclideanSpace ℂ (Fin n) := fun z => Ψi z (h z)
  have hgd : ContDiffOn ℝ ∞ g (ball 0 ρf) := hΨi.clm_apply (hh.mono hρ1')
  have hDΨi : ContinuousOn (fderiv ℝ Ψi) (ball 0 ρf) :=
    hΨi.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨CD1, hCD1⟩ := hKc.exists_bound_of_continuousOn
    ((hDΨi.clm_apply (continuousOn_const (c := (1 : ℂ)))).mono hK)
  obtain ⟨CDI, hCDI⟩ := hKc.exists_bound_of_continuousOn
    ((hDΨi.clm_apply (continuousOn_const (c := Complex.I))).mono hK)
  set CD := max CD1 CDI with hCD_def
  obtain ⟨Ci, hCi⟩ := hKc.exists_bound_of_continuousOn (hΨi.continuousOn.mono hK)
  obtain ⟨CΨ, hCΨ⟩ := hKc.exists_bound_of_continuousOn (hΨ.continuousOn.mono hK)
  have hMg : ∀ z ∈ ball (0 : ℂ) σ,
      ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤
        ((CD + CD + Ci * M') * CΨ) * ‖g z‖ := by
    intro z hz
    have hzK : z ∈ closedBall (0 : ℂ) σ := ball_subset_closedBall hz
    have hzρ : z ∈ ball (0 : ℂ) ρf := hK hzK
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
        fderiv ℝ Ψi z 1 (h z) + Complex.I • fderiv ℝ Ψi z Complex.I (h z) +
          Ψi z (fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)) := by
      rw [hfd, hfd, smul_add, hJ, map_add]
      abel
    have hhz : h z = Ψ z (g z) := (hr (h z)).symm
    have hnh : ‖h z‖ ≤ CΨ * ‖g z‖ := by
      rw [hhz]; exact (Ψ z).le_of_opNorm_le (hCΨ z hzK) _
    have hCi0 : 0 ≤ Ci := (norm_nonneg _).trans (hCi z hzK)
    have hM0 : 0 ≤ M' := le_max_right _ _
    have hCD0 : 0 ≤ CD := (norm_nonneg _).trans ((hCD1 z hzK).trans (le_max_left _ _))
    have e1 : ‖fderiv ℝ Ψi z 1 (h z)‖ ≤ CD * ‖h z‖ :=
      (fderiv ℝ Ψi z 1).le_of_opNorm_le ((hCD1 z hzK).trans (le_max_left _ _)) _
    have e2 : ‖Complex.I • fderiv ℝ Ψi z Complex.I (h z)‖ ≤ CD * ‖h z‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact (fderiv ℝ Ψi z Complex.I).le_of_opNorm_le ((hCDI z hzK).trans (le_max_right _ _)) _
    have e3 : ‖Ψi z (fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I))‖ ≤ Ci * M' * ‖h z‖ := by
      refine ((Ψi z).le_opNorm _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul (hCi z hzK) ?_ (norm_nonneg _) hCi0
      exact (hM z hz1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    rw [hsum]
    calc _ ≤ ‖fderiv ℝ Ψi z 1 (h z) + Complex.I • fderiv ℝ Ψi z Complex.I (h z)‖ +
          ‖Ψi z (fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I))‖ := norm_add_le _ _
      _ ≤ CD * ‖h z‖ + CD * ‖h z‖ + Ci * M' * ‖h z‖ := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add e1 e2)
      _ = (CD + CD + Ci * M') * ‖h z‖ := by ring
      _ ≤ (CD + CD + Ci * M') * (CΨ * ‖g z‖) := by
          gcongr
      _ = _ := by ring
  obtain ⟨ε, hε, Φ₀, f, hΦc, hΦb, hf, hgf⟩ :=
    exists_similarity_of_norm_dbar_le n σ _ hσ g
      ((hgd.mono ((ball_subset_closedBall).trans hK)).of_le (by simp)) hMg
  set ε' := min ε (σ / 2) with hε'_def
  have hε' : 0 < ε' := lt_min hε (by linarith)
  have hs1 : closedBall (0 : ℂ) ε' ⊆ closedBall 0 ε :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hs2 : closedBall (0 : ℂ) ε' ⊆ ball 0 ρf :=
    (closedBall_subset_closedBall ((min_le_right _ _).trans (by linarith))).trans hK
  have hε'1 : ε' < 1 := by
    have : ε' ≤ σ / 2 := min_le_right _ _
    linarith
  refine ⟨ε', hε', hε'1, fun z => (Ψ z).comp ((Φ₀ z).restrictScalars ℝ), f, ?_, ?_,
    hf.mono (ball_subset_ball (min_le_left _ _)), ?_⟩
  · have hR : ContinuousOn (fun z => (Φ₀ z).restrictScalars ℝ) (closedBall 0 ε') := by
      have := (ContinuousLinearMap.restrictScalarsIsometry ℂ (EuclideanSpace ℂ (Fin n))
        (EuclideanSpace ℂ (Fin n)) ℝ ℝ).continuous.comp_continuousOn (hΦc.mono hs1)
      exact this
    exact (hΨ.continuousOn.mono hs2).clm_comp hR
  · intro z hz
    obtain ⟨hl, hr, hI⟩ := hprop z (hs2 hz)
    have hΨb : Function.Bijective (Ψ z) :=
      ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
    refine ⟨hΨb.comp (hΦb z (hs1 hz)), fun w => ?_⟩
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
    exact hI _
  · intro z hz
    have hz' : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left _ _) hz
    obtain ⟨hl, hr, hI⟩ := hprop z (hs2 (ball_subset_closedBall hz))
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars']
    rw [← hgf z hz']
    exact (hr (h z)).symm

/-- Let `E` have real dimension `2n`, let `U ⊆ ℂ` be open and let `J̄ : U → End_ℝ(E)` be smooth with
`J̄(z)² = -1`. Let `h : U → E` be smooth with `‖∂ₛh + J̄(z) ∂ₜh‖ ≤ M ‖h‖` on `U`, and let `z₀ ∈ U`.
Then for some `ε > 0` with `B(z₀, ε) ⊆ U` there are a continuous `Θ : B̄(z₀, ε) → Hom_ℝ(ℂⁿ, E)`
with every `Θ(z)` bijective and `Θ(z) ∘ i = J̄(z) ∘ Θ(z)`, and a holomorphic
`f : B(z₀, ε) → ℂⁿ` with `h = Θ f` on `B(z₀, ε)`. -/
theorem exists_factorization_of_norm_dbar_le_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n)
    (Jbar : ℂ → E →L[ℝ] E) (U : Set ℂ) (hU : IsOpen U) (hJbar : ContDiffOn ℝ ∞ Jbar U)
    (hJbar2 : ∀ z ∈ U, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ ε > (0 : ℝ), ball z₀ ε ⊆ U ∧ ∃ Θ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Θ (closedBall z₀ ε) ∧
        (∀ z ∈ closedBall z₀ ε, Function.Bijective (Θ z) ∧
          ∀ w, Θ z (Complex.I • w) = Jbar z (Θ z w)) ∧
        DifferentiableOn ℂ f (ball z₀ ε) ∧ ∀ z ∈ ball z₀ ε, h z = Θ z (f z) := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set T : ℂ → ℂ := fun z => z₀ + R • z with hT
  have hTd : ∀ z, HasFDerivAt T (R • ContinuousLinearMap.id ℝ ℂ) z := fun z =>
    ((hasFDerivAt_id z).const_smul R).const_add z₀
  have hTc : ContDiff ℝ ∞ T := contDiff_const.add (contDiff_id.const_smul R)
  have hTm : ∀ z ∈ ball (0 : ℂ) 1, T z ∈ U := by
    intro z hz
    apply hRU
    rw [mem_ball, dist_eq_norm, hT, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [mem_ball, dist_zero_right] at hz
    nlinarith
  have hJb : ContDiffOn ℝ ∞ (fun z => Jbar (T z)) (ball 0 1) :=
    hJbar.comp hTc.contDiffOn hTm
  have hhb : ContDiffOn ℝ ∞ (fun z => h (T z)) (ball 0 1) := hh.comp hTc.contDiffOn hTm
  have hMb : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (fun z => h (T z)) z 1 +
      Jbar (T z) (fderiv ℝ (fun z => h (T z)) z Complex.I)‖ ≤ (R * M) * ‖h (T z)‖ := by
    intro z hz
    have hd : DifferentiableAt ℝ h (T z) :=
      (hh.differentiableOn (by simp) _ (hTm z hz)).differentiableAt (hU.mem_nhds (hTm z hz))
    have hfd : ∀ v, fderiv ℝ (fun z => h (T z)) z v = R • fderiv ℝ h (T z) v := by
      intro v
      have := (hd.hasFDerivAt.comp z (hTd z)).fderiv
      rw [show (fun z => h (T z)) = h ∘ T from rfl, this]
      simp
    rw [hfd, hfd, map_smul, ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hM _ (hTm z hz)) hR.le
  obtain ⟨ε, hε, hε1, Θ₀, f₀, hΘc, hΘb, hf, hhf⟩ :=
    c1k_unit n hn (fun z => Jbar (T z)) hJb (fun z hz => hJbar2 _ (hTm z hz)) _ hhb _ hMb
  set S : ℂ → ℂ := fun z => R⁻¹ • (z - z₀) with hS
  have hTS : ∀ z, T (S z) = z := fun z => by
    simp only [hT, hS, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]; abel
  have hSn : ∀ z, ‖S z‖ = R⁻¹ * dist z z₀ := fun z => by
    rw [hS, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, dist_eq_norm]
  have hSc : Continuous S := by rw [hS]; fun_prop
  have hSball : ∀ z, z ∈ ball z₀ (R * ε) ↔ S z ∈ ball (0 : ℂ) ε := fun z => by
    rw [mem_ball, mem_ball, dist_zero_right, hSn, inv_mul_lt_iff₀ hR]
  have hScl : ∀ z, z ∈ closedBall z₀ (R * ε) ↔ S z ∈ closedBall (0 : ℂ) ε := fun z => by
    rw [mem_closedBall, mem_closedBall, dist_zero_right, hSn, inv_mul_le_iff₀ hR]
  refine ⟨R * ε, mul_pos hR hε, fun z hz => ?_, fun z => Θ₀ (S z), fun z => f₀ (S z), ?_, ?_,
    ?_, ?_⟩
  · apply hRU
    rw [mem_ball] at hz ⊢
    nlinarith
  · exact hΘc.comp hSc.continuousOn fun z hz => (hScl z).1 hz
  · intro z hz
    have := hΘb (S z) ((hScl z).1 hz)
    rw [hTS] at this
    exact this
  · have hSd : Differentiable ℂ S := fun z =>
      ((differentiableAt_id.sub_const z₀).const_smul R⁻¹)
    exact hf.comp hSd.differentiableOn fun z hz => (hSball z).1 hz
  · intro z hz
    have := hhf (S z) ((hSball z).1 hz)
    rw [hTS] at this
    exact this

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n)
    (Jbar : ℂ → E →L[ℝ] E) (U : Set ℂ) (hU : IsOpen U) (hJbar : ContDiffOn ℝ ∞ Jbar U)
    (hJbar2 : ∀ z ∈ U, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ ε > (0 : ℝ), ball z₀ ε ⊆ U ∧ ∃ Θ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Θ (closedBall z₀ ε) ∧
        (∀ z ∈ closedBall z₀ ε, Function.Bijective (Θ z) ∧
          ∀ w, Θ z (Complex.I • w) = Jbar z (Θ z w)) ∧
        DifferentiableOn ℂ f (ball z₀ ε) ∧ ∀ z ∈ ball z₀ ε, h z = Θ z (f z) :=
  exists_factorization_of_norm_dbar_le_aux n hn Jbar U hU hJbar hJbar2 h hh M hM z₀ hz₀
