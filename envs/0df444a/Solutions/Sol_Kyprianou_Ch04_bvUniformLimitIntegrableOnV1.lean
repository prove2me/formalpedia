-- Prove2me | solution 1 for Kyprianou.Ch04.bvUniformLimitIntegrableOnV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:32:57.797796+00:00
-- url     : https://prove2.me/submissions/1a0fc11c-e87a-47a9-9cdb-0f97ef5b3b90

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I A : Type} [MeasurableSpace A] (L : Filter I) [L.NeBot]
    (μ : Measure A) (s : Set A) (hs : MeasurableSet s) (hμ : μ s < ⊤)
    (F : I → A → ℝ) (g : A → ℝ)
    (hF : ∀ i, IntegrableOn (F i) s μ)
    (hU : TendstoUniformlyOn F g L s) :
    IntegrableOn g s μ := by
  classical
  have hex (n : ℕ) : ∃ i, ∀ x ∈ s, dist (g x) (F i x) < 1 / ((n : ℝ) + 1) :=
    ((Metric.tendstoUniformlyOn_iff.mp hU) _ (by positivity)).exists
  choose i hi using hex
  have hN : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq (x : A) (hx : x ∈ s) : Tendsto (fun n => F (i n) x) atTop (nhds (g x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hN.eventually (gt_mem_nhds hε)] with n hn
    rw [dist_comm]
    exact (hi n x hx).trans hn
  have hm : AEStronglyMeasurable g (μ.restrict s) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hF (i n)).aestronglyMeasurable)
      ((ae_restrict_mem hs).mono fun x hx => hseq x hx)
  letI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hμ⟩
  have hmajor : Integrable (fun x => ‖F (i 0) x‖ + 1) (μ.restrict s) :=
    (hF (i 0)).norm.add (integrable_const 1)
  apply hmajor.mono' hm
  filter_upwards [ae_restrict_mem hs] with x hx
  have hh := hi 0 x hx
  simp only [Nat.cast_zero, zero_add, div_one, dist_eq_norm] at hh
  calc
    ‖g x‖ = ‖(g x - F (i 0) x) + F (i 0) x‖ := by rw [sub_add_cancel]
    _ ≤ ‖g x - F (i 0) x‖ + ‖F (i 0) x‖ := norm_add_le _ _
    _ ≤ _ := by linarith
