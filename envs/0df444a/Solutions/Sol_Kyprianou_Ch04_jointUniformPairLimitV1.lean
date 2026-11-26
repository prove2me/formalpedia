-- Prove2me | solution 1 for Kyprianou.Ch04.jointUniformPairLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:05:32.062157+00:00
-- url     : https://prove2.me/submissions/899f08d1-7888-4899-ae4b-e17df8da9085

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal Topology
set_option autoImplicit false

/-- Common compact Cauchy convergence identifies a given first-coordinate limit. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : ℕ → NNReal → Ω → ℝ) (X : NNReal → Ω → ℝ)
    (k : ℕ → ℕ)
    (hc : ∀ᵐ w ∂P, ∀ T : NNReal,
      UniformCauchySeqOn (fun n t => (U (k n) t w,V (k n) t w)) atTop (Icc 0 T))
    (hx : ∀ᵐ w ∂P, ∀ t, Tendsto (fun n => U (k n) t w) atTop (𝓝 (X t w))) :
    ∃ M : NNReal → Ω → ℝ,
      ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, t ≤ T →
          |U (k n) t w - X t w| < δ ∧ |V (k n) t w - M t w| < δ := by
  let M : NNReal → Ω → ℝ := fun t w => limUnder atTop (fun n => V (k n) t w)
  refine ⟨M,?_⟩
  filter_upwards [hc,hx] with w hcw hxw
  have hp (t : NNReal) : CauchySeq (fun n => (U (k n) t w,V (k n) t w)) := by
    apply Metric.cauchySeq_iff.mpr
    intro δ hδ
    obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp (hcw t) δ hδ
    exact ⟨N,fun m hm n hn => hN m hm n hn t ⟨zero_le,le_rfl⟩⟩
  have hv (t : NNReal) : Tendsto (fun n => V (k n) t w) atTop (𝓝 (M t w)) := by
    obtain ⟨p,hp⟩ := cauchySeq_tendsto_of_complete (hp t)
    have h : Tendsto (fun n => V (k n) t w) atTop (𝓝 p.2) :=
      continuous_snd.continuousAt.tendsto.comp hp
    change Tendsto _ _ (𝓝 (limUnder atTop (fun n => V (k n) t w)))
    rw [h.limUnder_eq]
    exact h
  intro T δ hδ
  have hu := (hcw T).tendstoUniformlyOn_of_tendsto
    (fun t _ => (hxw t).prodMk_nhds (hv t))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu δ hδ)
  refine ⟨N,fun n hn t ht => ?_⟩
  have h := hN n hn t ⟨zero_le,ht⟩
  simpa [Prod.dist_eq,Real.dist_eq,max_lt_iff,abs_sub_comm] using h
