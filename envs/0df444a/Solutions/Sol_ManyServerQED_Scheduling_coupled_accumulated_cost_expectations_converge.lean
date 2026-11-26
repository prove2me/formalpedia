-- Prove2me | solution 1 for ManyServerQED.Scheduling.coupled_accumulated_cost_expectations_converge
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:58:00.874161+00:00
-- url     : https://prove2.me/submissions/7465a062-f520-4377-97c7-903b09f9639a

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_nonnegative_cost_expectation_from_ae_limit_and_moment
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1250000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (T : ℝ≥0) (p : ℝ) (hp : 1 < p) (K : ℝ≥0∞) (hK : K < ⊤)
    (e : ℕ → Ω → ℝ≥0∞)
    (hCost : ∀ᶠ n in atTop, ∀ ω,
        0 ≤ Z n ω T (Fin.natAdd (k+k+k) (0 : Fin 2)) ∧
        ENNReal.ofReal (Z n ω T (Fin.natAdd (k+k+k) (0 : Fin 2))) = e n ω)
    (hMom : ∀ᶠ n in atTop, (∫⁻ ω, e n ω ^ p ∂P) ≤ K) :
    Integrable (d.runningCost T) d.Q ∧
      Tendsto (fun j => ∫⁻ ω, e (s (d.r j)) ω ∂P) atTop
        (𝓝 (ENNReal.ofReal (∫ ω, d.runningCost T ω ∂d.Q))) := by
  classical
  letI : IsProbabilityMeasure d.Q := d.isProb
  let n (j : ℕ) := s (d.r j)
  have hN : Tendsto n atTop atTop := hs.comp d.r_cofinal
  let i : Fin (k+k+k+2) := Fin.natAdd (k+k+k) (0 : Fin 2)
  let a (j : ℕ) (ω : Ω) := Z (n j) ω T i
  let b (j : ℕ) (ω : d.Ω') := d.row j ω T i
  let c : d.Ω' → ℝ := d.runningCost T
  let q (w : ℝ≥0 → Fin (k+k+k+2) → ℝ) := w T i
  have hq : Measurable q := (measurable_pi_apply i).comp (measurable_pi_apply T)
  have hLaw : ∀ᶠ j in atTop, IdentDistrib (b j) (a j) d.Q P :=
    d.row_law.mono (fun _ h => h.comp hq)
  obtain ⟨N,hcut⟩ := eventually_atTop.1
    (hLaw.and ((hN.eventually hCost).and (hN.eventually hMom)))
  let Y (j : ℕ) (ω : d.Ω') :=
    if h : N ≤ j then (hcut j h).1.aemeasurable_fst.mk (b j) ω else 0
  have hYm (j : ℕ) : Measurable (Y j) := by
    dsimp only [Y]
    split
    · exact AEMeasurable.measurable_mk _
    · exact measurable_const
  have hYlaw (j : ℕ) (hj : N ≤ j) : IdentDistrib (Y j) (a j) d.Q P := by
    have h := (hcut j hj).1
    refine ⟨(hYm j).aemeasurable,h.aemeasurable_snd,?_⟩
    have he : b j =ᵐ[d.Q] Y j := by simpa only [Y,dif_pos hj] using h.aemeasurable_fst.ae_eq_mk
    rw [← Measure.map_congr he,h.map_eq]
  have hNon (j : ℕ) : ∀ᵐ ω ∂d.Q, 0 ≤ Y j ω := by
    by_cases hj : N ≤ j
    · have h := hYlaw j hj
      have hS : MeasurableSet (Iio (0:ℝ)) := measurableSet_Iio
      have he := congrArg (fun μ : Measure ℝ => μ (Iio 0)) h.map_eq
      rw [Measure.map_apply (hYm j) hS,Measure.map_apply_of_aemeasurable h.aemeasurable_snd hS] at he
      have hEmp : a j ⁻¹' Iio (0:ℝ) = ∅ := by
        ext ω
        simp only [mem_preimage,mem_Iio,notMem_empty,iff_false,not_lt]
        exact ((hcut j hj).2.1 ω).1
      rw [hEmp,measure_empty] at he
      apply ae_iff.2
      have eq : {ω | ¬ 0 ≤ Y j ω} = Y j ⁻¹' Iio (0:ℝ) := by
        ext ω
        exact not_le
      rw [eq]
      exact he
    · exact Eventually.of_forall (fun ω => by simp [Y,hj])
  have hCa : ∀ᵐ ω ∂d.Q, Tendsto (fun j => Y j ω) atTop (𝓝 (c ω)) := by
    have hA (j : ℕ) : ∀ᵐ ω ∂d.Q, N ≤ j → Y j ω = b j ω := by
      by_cases hj : N ≤ j
      · filter_upwards [(hcut j hj).1.aemeasurable_fst.ae_eq_mk] with ω h _
        simpa only [Y,dif_pos hj] using h.symm
      · exact Eventually.of_forall (fun _ h => (hj h).elim)
    filter_upwards [d.convergence,ae_all_iff.2 hA] with ω hω hA
    refine (show Tendsto (fun j => b j ω) atTop (𝓝 (c ω)) from ?_).congr' ?_
    · have hs := hω T T.2
      apply Metric.tendsto_nhds.2
      intro ε hε
      filter_upwards [(tendsto_order.1 hs).2 _ (ENNReal.ofReal_pos.2 hε)] with j hj
      have hFin : |b j ω-c ω| ≤ ∑ q, |d.row j ω T q-d.limit ω T q| :=
        Finset.single_le_sum (f := fun q => |d.row j ω T q-d.limit ω T q|)
          (fun q _ => abs_nonneg _) (Finset.mem_univ i)
      have hPt := (ENNReal.ofReal_le_ofReal hFin).trans
        (le_iSup_of_le (T:ℝ) (le_iSup_of_le ⟨T.2,le_rfl⟩ le_rfl) :
          ENNReal.ofReal (∑ q, |d.row j ω T q-d.limit ω T q|) ≤
          supDist (d.row j ω) (d.limit ω) T)
      rw [Real.dist_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hPt.trans_lt hj)
    · filter_upwards [eventually_ge_atTop N] with j hj
      exact (hA j hj).symm
  have hCn : ∀ᵐ ω ∂d.Q, 0 ≤ c ω := by
    filter_upwards [hCa,ae_all_iff.2 hNon] with ω hω h'
    exact ge_of_tendsto' hω h'
  have hR (j : ℕ) (hj : N ≤ j) (q : ℝ) :
      (∫⁻ ω, ENNReal.ofReal (Y j ω)^q ∂d.Q) =
        ∫⁻ ω, e (n j) ω^q ∂P := by
    let v (x : ℝ) := ENNReal.ofReal x ^ q
    have hv : Measurable v := ENNReal.measurable_ofReal.pow_const _
    have h := hYlaw j hj
    calc
      _ = ∫⁻ x, v x ∂Measure.map (Y j) d.Q := (lintegral_map hv (hYm j)).symm
      _ = ∫⁻ x, v x ∂Measure.map (a j) P := by rw [h.map_eq]
      _ = ∫⁻ ω, v (a j ω) ∂P := lintegral_map' hv.aemeasurable h.aemeasurable_snd
      _ = _ := lintegral_congr (fun ω => by
        change ENNReal.ofReal (a j ω)^q = _
        rw [((hcut j hj).2.1 ω).2])
  have hRp : ∀ᶠ j in atTop, (∫⁻ ω, ENNReal.ofReal (Y j ω)^p ∂d.Q) ≤ K := by
    filter_upwards [eventually_ge_atTop N] with j hj
    rw [hR j hj p]
    exact (hcut j hj).2.2
  obtain ⟨hCi,hCL⟩ := nonnegative_cost_expectation_from_ae_limit_and_moment d.Q Y c hYm
    ((measurable_pi_apply i).comp (d.limit_meas T)) hNon hCn hCa p hp K hK hRp
  refine ⟨hCi,hCL.congr' ?_⟩
  filter_upwards [eventually_ge_atTop N] with j hj
  simpa only [ENNReal.rpow_one] using hR j hj 1
