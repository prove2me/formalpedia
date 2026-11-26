-- Prove2me | solution 1 for ManyServerQED.Scheduling.coupled_real_accumulators_preserve_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:35.62639+00:00
-- url     : https://prove2.me/submissions/c194d9ba-efe1-4974-b537-5a35f8aa6ba2

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1350000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (v : (Fin (k+k+k+2) → ℝ) → ℝ) (hv : Continuous v)
    (h : ∀ᶠ n in atTop, ∀ ω, MonotoneOn (fun t => v (Z n ω t)) (Ici (0:ℝ))) :
    ∀ᵐ ω ∂d.Q, Monotone (fun t : ℝ≥0 => v (d.limit ω t)) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.1 (d.row_law.and ((hs.comp d.r_cofinal).eventually h))
  have hQ (n : ℕ) (a b : ℚ) : ∀ᵐ ω ∂d.Q, N ≤ n →
      (a:ℝ).toNNReal ≤ (b:ℝ).toNNReal →
        v (d.row n ω ((a:ℝ).toNNReal:ℝ)) ≤ v (d.row n ω ((b:ℝ).toNNReal:ℝ)) := by
    by_cases hn : N ≤ n
    · by_cases hab : (a:ℝ).toNNReal ≤ (b:ℝ).toNNReal
      · let B : Set (ℝ≥0 → Fin (k+k+k+2) → ℝ) :=
          {p | v (p (b:ℝ).toNNReal) < v (p (a:ℝ).toNNReal)}
        have hB : MeasurableSet B := measurableSet_lt (hv.measurable.comp (measurable_pi_apply _))
          (hv.measurable.comp (measurable_pi_apply _))
        have hEq := (hN n hn).1.measure_mem_eq hB
        have hEmp : {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ B} = ∅ := by
          apply eq_empty_iff_forall_notMem.2
          intro ω hω
          exact (not_lt_of_ge ((hN n hn).2 ω (a:ℝ).toNNReal.2 (b:ℝ).toNNReal.2
            (by exact_mod_cast hab))) hω
        change d.Q {ω | (fun t : ℝ≥0 => d.row n ω t) ∈ B} =
          P {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ B} at hEq
        rw [hEmp,measure_empty] at hEq
        simpa only [hn,hab,true_implies] using
          (ae_iff.2 (show d.Q {ω | ¬ (v (d.row n ω ((a:ℝ).toNNReal:ℝ)) ≤
            v (d.row n ω ((b:ℝ).toNNReal:ℝ)))} = 0 by simpa only [not_le,B,mem_setOf_eq] using hEq))
      · exact Eventually.of_forall (fun _ _ h => (hab h).elim)
    · exact Eventually.of_forall (fun _ h _ => (hn h).elim)
  have hAe : ∀ᵐ ω ∂d.Q, ∀ (n : ℕ) (a b : ℚ), N ≤ n →
      (a:ℝ).toNNReal ≤ (b:ℝ).toNNReal →
        v (d.row n ω ((a:ℝ).toNNReal:ℝ)) ≤ v (d.row n ω ((b:ℝ).toNNReal:ℝ)) :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun a => ae_all_iff.2 (hQ n a)))
  filter_upwards [hAe,d.convergence] with ω hw hConv
  let g (t : ℝ) := v (d.limit ω (t.toNNReal:ℝ))
  have hg : Continuous g := hv.comp ((d.limit_cont ω).comp_continuous
    ((continuous_subtype_val : Continuous (fun r : ℝ≥0 => (r:ℝ))).comp continuous_real_toNNReal)
      (fun t => t.toNNReal.2))
  have hG (a b : ℚ) (hab : (a:ℝ).toNNReal ≤ (b:ℝ).toNNReal) : g a ≤ g b := by
    have hL (t : ℝ≥0) : Tendsto (fun n => v (d.row n ω t)) atTop (𝓝 (v (d.limit ω t))) := by
      apply hv.continuousAt.tendsto.comp
      apply tendsto_pi_nhds.2
      intro i
      apply Metric.tendsto_nhds.2
      intro ε hε
      filter_upwards [(tendsto_order.1 (hConv t t.2)).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
      rw [Real.dist_eq]
      have h := Finset.single_le_sum (f := fun j => |d.row n ω t j-d.limit ω t j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      exact (ENNReal.ofReal_lt_ofReal_iff hε).1
        (((ENNReal.ofReal_le_ofReal h).trans (le_iSup₂_of_le (t:ℝ) ⟨t.2,le_rfl⟩ le_rfl)).trans_lt hn)
    apply le_of_tendsto_of_tendsto (hL (a:ℝ).toNNReal) (hL (b:ℝ).toNNReal)
    exact (eventually_ge_atTop N).mono fun n hn => hw n a b hn hab
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ p.1 ∨ g p.1 ≤ g p.2}
  have hSc : IsClosed S :=
    (isClosed_le continuous_snd continuous_fst).union
      (isClosed_le (hg.comp continuous_fst) (hg.comp continuous_snd))
  have hRat := (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))).prodMap
    (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ)))
  have hSub : range (Prod.map (fun q : ℚ => (q:ℝ)) (fun q : ℚ => (q:ℝ))) ⊆ S := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    rcases le_total (a:ℝ) (b:ℝ) with hab | hab
    · exact Or.inr (hG a b (Real.toNNReal_mono hab))
    · exact Or.inl hab
  have hAll := closure_minimal hSub hSc
  rw [hRat.closure_range] at hAll
  intro a b hab
  rcases lt_or_eq_of_le hab with hab | hab
  · have hh : ((a:ℝ),(b:ℝ)) ∈ S := hAll (mem_univ _)
    rcases hh with hh | hh
    · exact (not_le_of_gt (by exact_mod_cast hab : (a:ℝ) < b) hh).elim
    · simpa only [g,Real.toNNReal_coe] using hh
  · rw [hab]
