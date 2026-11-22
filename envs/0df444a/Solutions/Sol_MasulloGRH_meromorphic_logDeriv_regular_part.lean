-- Prove2me | solution 1 for MasulloGRH.meromorphic_logDeriv_regular_part
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:54:03.280724+00:00
-- url     : https://prove2.me/submissions/c7dafd57-9439-4e46-a1e1-05c34714755f

import Mathlib

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace PrincipalPartCancellationProof

/-- At any finite-order zero or pole, subtracting the principal part from the
actual logarithmic derivative leaves an analytic germ. The equality is on a
punctured neighborhood, so it does not impose a value on the original function
or its totalized derivative at the singular point. -/
theorem exists_analytic_logDeriv_regular_part
    (f : ℂ → ℂ) (p : ℂ) (n : ℤ)
    (hf : MeromorphicAt f p) (hn : meromorphicOrderAt f p = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      (fun z : ℂ => deriv f z / f z - (n : ℂ) / (z - p)) =ᶠ[𝓝[≠] p] g := by
  obtain ⟨h, hha, hhne, hfh⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  let g : ℂ → ℂ := fun z => deriv h z / h z
  refine ⟨g, hha.deriv.div hha hhne, ?_⟩
  have hfh' : f =ᶠ[𝓝[≠] p] (fun z => (z - p) ^ n * h z) := by
    filter_upwards [hfh] with z hz
    simpa only [smul_eq_mul] using hz
  have heq := logDeriv_congr_nhdsNE hfh'
  filter_upwards [heq,
    hha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hha.continuousAt.eventually_ne hhne).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z hz hhz hhz0 hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - p) z := by fun_prop
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (w - p) ^ n) z := by
    exact hsub.zpow (Or.inl hzp')
  change logDeriv f z - (n : ℂ) / (z - p) = logDeriv h z
  rw [hz, logDeriv_mul (f := fun w : ℂ => (w - p) ^ n) (g := h) z
    (zpow_ne_zero n hzp') hhz0 hpow hhz.differentiableAt,
    logDeriv_fun_zpow (f := fun w : ℂ => w - p) hsub n]
  have hshift : logDeriv (fun w : ℂ => w - p) z = 1 / (z - p) := by
    simp [logDeriv_apply]
  rw [hshift, mul_one_div]
  ring

/-- The regular part is bounded on a sufficiently small punctured ball. The
finite-order hypothesis rules out the identically zero meromorphic germ. -/
theorem exists_pos_logDeriv_regular_part_bound
    (f : ℂ → ℂ) (p : ℂ) (n : ℤ)
    (hf : MeromorphicAt f p) (hn : meromorphicOrderAt f p = n) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ z : ℂ, 0 < ‖z - p‖ → ‖z - p‖ < ε →
        ‖deriv f z / f z - (n : ℂ) / (z - p)‖ ≤ C := by
  obtain ⟨g, hga, heq⟩ := exists_analytic_logDeriv_regular_part f p n hf hn
  have hgb : ∀ᶠ z in 𝓝 p, ‖g z‖ < ‖g p‖ + 1 :=
    hga.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hb : ∀ᶠ z in 𝓝[≠] p,
      ‖deriv f z / f z - (n : ℂ) / (z - p)‖ ≤ ‖g p‖ + 1 := by
    filter_upwards [heq, hgb.filter_mono nhdsWithin_le_nhds] with z hz hgz
    rw [hz]
    exact le_of_lt hgz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hb
  refine ⟨ε, ‖g p‖ + 1, hε, by positivity, ?_⟩
  intro z hpos hlt
  exact hball ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hlt,
    sub_ne_zero.mp (norm_pos_iff.mp hpos)⟩

end PrincipalPartCancellationProof

theorem solution
    (f : ℂ → ℂ) (p : ℂ) (n : ℤ)
    (hf : MeromorphicAt f p) (hn : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ((fun z : ℂ => deriv f z / f z - (n : ℂ) / (z - p)) =ᶠ[𝓝[≠] p] g) ∧
      ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
        ∀ z : ℂ, 0 < ‖z - p‖ → ‖z - p‖ < ε →
          ‖deriv f z / f z - (n : ℂ) / (z - p)‖ ≤ C := by
  obtain ⟨g, hga, heq⟩ := _root_.PrincipalPartCancellationProof.exists_analytic_logDeriv_regular_part f p n hf hn
  exact ⟨g, hga, heq, _root_.PrincipalPartCancellationProof.exists_pos_logDeriv_regular_part_bound f p n hf hn⟩

#print axioms solution
