-- Prove2me | solution 1 for JHolomorphic.exists_holomorphic_norm_comparable_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T14:45:36.820435+00:00
-- url     : https://prove2.me/submissions/a1d22ddc-b3b9-4942-8314-d59a1ec7cc17

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_JHolomorphic_exists_local_complex_frame
import Theorems.Thm_JHolomorphic_exists_similarity_of_norm_dbar_le
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff

/-- A smooth `h` with `‖∂ₛh + J̄(z) ∂ₜh‖ ≤ M ‖h‖` near `0` is, near `0`, comparable in norm to a
holomorphic `ℂⁿ`-valued map. -/
theorem exists_holomorphic_norm_comparable_of_norm_dbar_le_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1)) (ρ M : ℝ) (hρ : 0 < ρ)
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, ∃ f : ℂ → EuclideanSpace ℂ (Fin n),
      DifferentiableOn ℂ f (ball 0 ε) ∧
        ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖h z‖ ∧ ‖h z‖ ≤ C * ‖f z‖ := by
  obtain ⟨ρf, hρf, hρf1, Ψ, Ψi, hΨ, hΨi, hprop⟩ := exists_local_complex_frame n hn Jbar hJbar hJbar2
  have hρ1' : ball (0 : ℂ) ρf ⊆ ball 0 1 := ball_subset_ball hρf1
  set σ := min (ρf / 2) (ρ / 2) with hσ_def
  have hσ : 0 < σ := lt_min (by linarith) (by linarith)
  have hK : closedBall (0 : ℂ) σ ⊆ ball 0 ρf :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hKρ : closedBall (0 : ℂ) σ ⊆ ball 0 ρ :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
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
      exact (hM z (hKρ hzK)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
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
  have hs2 : closedBall (0 : ℂ) ε' ⊆ closedBall 0 σ :=
    closedBall_subset_closedBall ((min_le_right _ _).trans (by linarith))
  have hKε : IsCompact (closedBall (0 : ℂ) ε') := isCompact_closedBall _ _
  -- uniform upper bound on `Φ₀`
  obtain ⟨CΦ, hCΦ⟩ := hKε.exists_bound_of_continuousOn (hΦc.mono hs1)
  -- uniform lower bound on `Φ₀`
  have hlow : ∃ c > (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) ε', ∀ w : EuclideanSpace ℂ (Fin n),
      c * ‖w‖ ≤ ‖Φ₀ z w‖ := by
    set S := closedBall (0 : ℂ) ε' ×ˢ sphere (0 : EuclideanSpace ℂ (Fin n)) 1
    have hSc : IsCompact S := hKε.prod (isCompact_sphere _ _)
    have hcont : ContinuousOn (fun p : ℂ × EuclideanSpace ℂ (Fin n) => ‖Φ₀ p.1 p.2‖) S :=
      (((hΦc.mono hs1).comp continuousOn_fst (fun p hp => hp.1)).clm_apply
        continuousOn_snd).norm
    rcases S.eq_empty_or_nonempty with hS | hS
    · refine ⟨1, one_pos, fun z hz w => ?_⟩
      by_cases hw : w = 0
      · simp [hw]
      · exfalso
        have hmem : ((z, ((‖w‖⁻¹ : ℝ) : ℂ) • w) : ℂ × EuclideanSpace ℂ (Fin n)) ∈ S := by
          refine ⟨hz, ?_⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]
        rw [hS] at hmem
        exact hmem
    · obtain ⟨p, hpS, hpmin⟩ := hSc.exists_isMinOn hS hcont
      have hp2 : p.2 ≠ 0 := by
        intro h0
        have := hpS.2
        rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
        exact zero_ne_one this
      have hc : 0 < ‖Φ₀ p.1 p.2‖ := by
        refine norm_pos_iff.2 fun h0 => hp2 ?_
        exact (hΦb p.1 (hs1 hpS.1)).1 (h0.trans (map_zero _).symm)
      refine ⟨_, hc, fun z hz w => ?_⟩
      by_cases hw : w = 0
      · simp [hw]
      · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
        have hmem : ((z, ((‖w‖⁻¹ : ℝ) : ℂ) • w) : ℂ × EuclideanSpace ℂ (Fin n)) ∈ S := by
          refine ⟨hz, ?_⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_norm, inv_mul_cancel₀ hwpos.ne']
        have := hpmin hmem
        simp only [Set.mem_setOf_eq, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm] at this
        have key : ‖Φ₀ p.1 p.2‖ ≤ ‖w‖⁻¹ * ‖Φ₀ z w‖ := this
        calc ‖Φ₀ p.1 p.2‖ * ‖w‖ ≤ (‖w‖⁻¹ * ‖Φ₀ z w‖) * ‖w‖ :=
              mul_le_mul_of_nonneg_right key hwpos.le
          _ = ‖Φ₀ z w‖ := by field_simp
  obtain ⟨c, hc, hcw⟩ := hlow
  have hCi0 : 0 ≤ Ci := (norm_nonneg _).trans (hCi 0 (mem_closedBall_self hσ.le))
  have hCΨ0 : 0 ≤ CΨ := (norm_nonneg _).trans (hCΨ 0 (mem_closedBall_self hσ.le))
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg _).trans (hCΦ 0 (mem_closedBall_self hε'.le))
  refine ⟨ε', hε', max (c⁻¹ * Ci) (CΨ * CΦ), f, hf.mono (ball_subset_ball (min_le_left _ _)),
    fun z hz => ?_⟩
  have hzK : z ∈ closedBall (0 : ℂ) ε' := ball_subset_closedBall hz
  have hz' : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left _ _) hz
  have hgz : g z = Φ₀ z (f z) := hgf z hz'
  obtain ⟨hl, hr, hI⟩ := hprop z (hK (hs2 hzK))
  have hhz : h z = Ψ z (Φ₀ z (f z)) := by rw [← hgz]; exact (hr (h z)).symm
  constructor
  · have h1 : c * ‖f z‖ ≤ ‖g z‖ := hgz ▸ hcw z hzK (f z)
    have h2 : ‖g z‖ ≤ Ci * ‖h z‖ := (Ψi z).le_of_opNorm_le (hCi z (hs2 hzK)) _
    have h3 : ‖f z‖ ≤ c⁻¹ * Ci * ‖h z‖ := by
      rw [mul_assoc, le_inv_mul_iff₀ hc]
      exact h1.trans h2
    exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have h1 : ‖h z‖ ≤ CΨ * ‖Φ₀ z (f z)‖ := by
      rw [hhz]; exact (Ψ z).le_of_opNorm_le (hCΨ z (hs2 hzK)) _
    have h2 : ‖Φ₀ z (f z)‖ ≤ CΦ * ‖f z‖ := (Φ₀ z).le_of_opNorm_le (hCΦ z hzK) _
    calc ‖h z‖ ≤ CΨ * (CΦ * ‖f z‖) := h1.trans (mul_le_mul_of_nonneg_left h2 hCΨ0)
      _ = CΨ * CΦ * ‖f z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end JHolomorphic

open JHolomorphic

open Metric Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1)) (ρ M : ℝ) (hρ : 0 < ρ)
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, ∃ f : ℂ → EuclideanSpace ℂ (Fin n),
      DifferentiableOn ℂ f (ball 0 ε) ∧
        ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖h z‖ ∧ ‖h z‖ ≤ C * ‖f z‖ :=
  exists_holomorphic_norm_comparable_of_norm_dbar_le_aux n hn Jbar hJbar hJbar2 h hh ρ M hρ hM
