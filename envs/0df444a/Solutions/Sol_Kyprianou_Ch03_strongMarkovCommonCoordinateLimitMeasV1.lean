-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCommonCoordinateLimitMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:52:41.899807+00:00
-- url     : https://prove2.me/submissions/0ab1b002-f5fb-44a0-b3e3-74c2dcb1d0ba

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (Y : ℕ → Omega → (NNReal → Real)) (Z : Omega → (NNReal → Real))
    (hMeas : ∀ n, Measurable (Y n))
    (hLimit : ∀ᵐ w ∂mu, ∀ u : NNReal,
      Tendsto (fun n => Y n w u) atTop (nhds (Z w u))) :
    AEMeasurable Z mu := by
  classical
  obtain ⟨N, hSub, hN, hNull⟩ := exists_measurable_superset_of_null (ae_iff.mp hLimit)
  let W : Omega → (NNReal → ℝ) := fun w => if w ∈ N then 0 else Z w
  have hEq : W =ᵐ[mu] Z := by
    have hOutside : ∀ᵐ w ∂mu, w ∉ N := by
      rw [ae_iff]
      simpa using hNull
    filter_upwards [hOutside] with w hw
    simp [W, hw]
  have hW : Measurable W := by
    apply measurable_pi_iff.mpr
    intro u
    let g : ℕ → Omega → ℝ := fun n w => if w ∈ N then 0 else Y n w u
    apply measurable_of_tendsto_metrizable (f := g)
    · intro n
      exact measurable_const.piecewise hN ((measurable_pi_apply u).comp (hMeas n))
    · apply tendsto_pi_nhds.mpr
      intro w
      by_cases hw : w ∈ N
      · simpa [g, W, hw] using (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      · have hgood : ∀ u : NNReal, Tendsto (fun n => Y n w u) atTop (nhds (Z w u)) :=
          not_not.mp (fun hn => hw (hSub hn))
        simpa [g, W, hw] using hgood u
  exact hW.aemeasurable.congr hEq
