-- Prove2me | solution 2 for NoHair.israel_static_vacuum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:08:59.4363+00:00
-- url     : https://prove2.me/submissions/d911b36e-0d5d-4a2a-9c2f-70f2453487ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_vacuum_spherical_chart
import Theorems.Thm_NoHair_ingoing_areal_angular_ricci

open scoped ContDiff Manifold
open Set NoHair

private lemma vacuum_lapse {A : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn A (Ici R)) (h0 : A R = 0)
    (hd : ∀ r, R < r → DifferentiableAt ℝ A r)
    (hRic : ∀ r, R < r → 1 - A r - r * deriv A r = 0) :
    ∀ r, R < r → 1 - A r = R / r := by
  let f := fun r : ℝ => r * (1 - A r)
  have hf (r : ℝ) (hr : R < r) : HasDerivAt f 0 r := by
    apply ((hasDerivAt_id' r).fun_mul
      ((hasDerivAt_const r (1 : ℝ)).fun_sub (hd r hr).hasDerivAt)).congr_deriv
    linarith only [hRic r hr]
  obtain ⟨c, hconst⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero (f := f)
    (s := Ioi R) isPreconnected_Ioi
    (fun _ hr => (hf _ hr).differentiableAt.differentiableWithinAt) (fun _ hr => (hf _ hr).deriv)
  have hcl : EqOn f (fun _ => c) (Ici R) :=
    (show EqOn f (fun _ => c) (Ioi R) from fun _ hr => hconst _ hr).of_subset_closure
      (continuousOn_id.mul (continuousOn_const.sub hc)) continuousOn_const
      Ioi_subset_Ici_self (by rw [closure_Ioi])
  have hboundary := hcl (Set.mem_Ici.mpr (le_refl R))
  change R * (1 - A R) = c at hboundary
  simp only [h0, sub_zero, mul_one] at hboundary
  intro r hr
  apply (eq_div_iff (hR.trans hr).ne').2
  rw [mul_comm, hboundary]
  exact hconst r hr

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m : ℝ, 0 < m ∧ IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 0 := by
  obtain ⟨S, hd, hRic⟩ := static_vacuum_spherical_chart g F T φ E h hvac hstatic
  have profile := vacuum_lapse S.radius_pos S.lapse_continuous S.lapse_horizon hd
    (fun r hr => (ingoing_areal_angular_ricci S.lapseSq S.horizonRadius r
      (S.radius_pos.trans hr) hr hd).symm.trans (hRic r hr))
  let m := S.horizonRadius / 2
  have hm : 0 < m := half_pos S.radius_pos
  have radius : kerrNewmanOuterRadius m 0 0 = S.horizonRadius := by
    simp only [kerrNewmanOuterRadius, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq hm.le]
    dsimp only [m]
    ring
  refine ⟨m, hm, 0, S.chart, ?_, ?_⟩
  · simpa only [kerrNewmanDOC, radius] using S.diffeo
  · intro y hy
    have hr : S.horizonRadius < ksRadius 0 y := by
      simpa only [kerrNewmanDOC, Set.mem_setOf_eq, radius] using hy
    have hprof : ksProfile m 0 0 y = S.horizonRadius / ksRadius 0 y := by
      simp only [ksProfile, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, add_zero, m]
      field_simp [(S.radius_pos.trans hr).ne'] <;> ring
    constructor
    · rw [S.metric_coeffs y hr]
      ext i j
      simp only [kerrNewmanMetric, hprof, profile _ hr]
    · ext i j
      simp [pullbackCoeffs, hvac, kerrNewmanField, kerrNewmanPotential, coordPartial]
