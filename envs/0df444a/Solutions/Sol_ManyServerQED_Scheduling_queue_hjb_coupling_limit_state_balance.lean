-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_coupling_limit_state_balance
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:33.941313+00:00
-- url     : https://prove2.me/submissions/d801e1d2-696a-492f-8aaa-256a878ab5c1

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_diffusion_drift_remainder_uoc
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_at_zero
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem coupled_zero_of_scalar_observation {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {P : Measure Ω} {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (T : ℝ≥0) (φ : (Fin (k+k+k+2) → ℝ) → ℝ) (hφ : Continuous φ)
    (h : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ε ≤ |φ (Z n ω T)|}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂d.Q, φ (d.limit ω T) = 0 := by
  letI : IsProbabilityMeasure d.Q := d.isProb
  obtain ⟨N,hN⟩ := eventually_atTop.1 d.row_law
  let j (n : ℕ) := n+N
  let q (n : ℕ) (ω : d.Ω') := φ (d.row (j n) ω T)
  let q' (n : ℕ) (ω : Ω) := φ (Z (s (d.r (j n))) ω T)
  let a (ω : d.Ω') := φ (d.limit ω T)
  have hJ : Tendsto j atTop atTop := tendsto_add_atTop_nat N
  let ev (p : ℝ≥0 → Fin (k+k+k+2) → ℝ) := φ (p T)
  have hEv : Measurable ev := hφ.measurable.comp (measurable_pi_apply T)
  have hLaw (n : ℕ) : IdentDistrib (q n) (q' n) d.Q P :=
    (hN (j n) (by dsimp [j]; omega)).comp hEv
  have hAe : ∀ᵐ ω ∂d.Q, Tendsto (fun n => q n ω) atTop (𝓝 (a ω)) := by
    filter_upwards [d.convergence] with ω hω
    apply hφ.continuousAt.tendsto.comp
    apply tendsto_pi_nhds.2
    intro i
    have hSup := (hω (T:ℝ) T.2).comp hJ
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [(tendsto_order.1 hSup).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
    have hs : |d.row (j n) ω T i-d.limit ω T i| ≤
        ∑ l, |d.row (j n) ω T l-d.limit ω T l| :=
      Finset.single_le_sum (f := fun l => |d.row (j n) ω T l-d.limit ω T l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ i)
    have hU : ENNReal.ofReal |d.row (j n) ω T i-d.limit ω T i| ≤
        supDist (d.row (j n) ω) (d.limit ω) (T:ℝ) :=
      (ENNReal.ofReal_le_ofReal hs).trans (le_iSup_of_le (T:ℝ) (le_iSup_of_le ⟨T.2,le_rfl⟩ le_rfl))
    rw [Real.dist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hU.trans_lt hn)
  have hQ : TendstoInMeasure d.Q q atTop a :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hLaw n).aemeasurable_fst.aestronglyMeasurable) hAe
  have hq0 : TendstoInMeasure d.Q q atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hT := (h ε hε).comp (hs.comp (d.r_cofinal.comp hJ))
    refine hT.congr' (Eventually.of_forall fun n => ?_)
    let A : Set ℝ := {x | ε ≤ |x|}
    have hA : MeasurableSet A := measurableSet_le measurable_const measurable_id.abs
    simp only [sub_zero,Real.norm_eq_abs]
    exact ((hLaw n).measure_mem_eq (s := A) hA).symm
  exact tendstoInMeasure_ae_unique hQ hq0

set_option maxHeartbeats 1700000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M L γ u0 f X Ψ) s) :
    (∀ᵐ ω ∂d.Q, d.state 0 ω = x) ∧
    (∀ᵐ ω ∂d.Q, d.driftIntegral 0 ω = 0) ∧
    (∀ᵐ ω ∂d.Q, d.runningCost 0 ω = 0) ∧
    (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0,
      d.state t ω = x+(fun i => M.diffData.r i*d.noise t ω i)+d.driftIntegral t ω) := by
  letI : IsProbabilityMeasure d.Q := d.isProb
  let Z := queueHJBObservation M L γ u0 f X Ψ
  let D := M.diffData
  let e (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    M.Xhat n (X n) ω t i - M.Xhat0 n (X0 n) i -
      (M.Ahat n ω t i-M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i -
        M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i) -
      ∫ s in (0:ℝ)..t, drift D (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i
  have he : UocInProb M.P e (fun _ => 0) :=
    queue_diffusion_drift_remainder_uoc M X0 x hX0 X Ψ hC hWork u0
  let ix (i : Fin k) : Fin (k+k+k+2) := Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i))
  let iw (i : Fin k) : Fin (k+k+k+2) := Fin.castAdd 2 (Fin.castAdd k (Fin.natAdd k i))
  let ia (i : Fin k) : Fin (k+k+k+2) := Fin.castAdd 2 (Fin.natAdd (k+k) i)
  let ic : Fin (k+k+k+2) := Fin.natAdd (k+k+k) (0:Fin 2)
  have hIx (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      Z n ω t (ix i) = M.Xhat n (X n) ω t i := by
    simp only [ix,Z,queueHJBObservation,Fin.append_left]
  have hA (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      Z n ω t (ia i) = ∫ s in (0:ℝ)..t,
        drift D (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i := by
    simp only [ia,Z,queueHJBObservation,Fin.append_left,Fin.append_right,D]
  have hW (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      D.r i*Z n ω t (iw i) = M.Ahat n ω t i -
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i -
        M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i := by
    simp only [iw,Z,queueHJBObservation,Fin.append_left,Fin.append_right,D]
    field_simp [(M.diffData.r_pos i).ne']
    ring
  have hInit (i : Fin k) : ∀ᵐ ω ∂d.Q, d.state 0 ω i-x i = 0 := by
    let φ (z : Fin (k+k+k+2) → ℝ) := z (ix i)-x i
    have hφ : Continuous φ := (continuous_apply _).sub continuous_const
    apply coupled_zero_of_scalar_observation d hs 0 φ hφ
    intro ε hε
    let g (n : ℕ) := M.Xhat0 n (X0 n) i-x i
    have h := ((continuous_apply i).continuousAt.tendsto.comp hX0).sub
      (tendsto_const_nhds (x := x i))
    have ht : ∀ᶠ n in atTop, |g n| < ε := by
      have h' := Metric.tendsto_nhds.1 (by simpa only [g,Function.comp_apply,sub_self] using h :
        Tendsto g atTop (𝓝 (0:ℝ))) ε hε
      simpa only [Real.dist_eq,sub_zero] using h'
    apply tendsto_const_nhds.congr'
    filter_upwards [ht,eventually_ge_atTop 1] with n ht hn
    have hE : {ω | ε ≤ |φ (Z n ω 0)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro ω hw
      change ε ≤ |φ (Z n ω 0)| at hw
      rw [show φ (Z n ω 0) = g n by
        dsimp only [Z]
        rw [queue_hjb_observation_at_zero M L γ u0 f X Ψ X0 n (hC n hn) ω]
        simp only [φ,ix,Fin.append_left,g]] at hw
      exact (not_le_of_gt ht) hw
    change 0 = M.P {ω | ε ≤ |φ (Z n ω 0)|}
    rw [hE,measure_empty]
  have hZero (idx : Fin (k+k+k+2))
      (hi : ∀ n, 1 ≤ n → ∀ ω, Z n ω 0 idx = 0) :
      ∀ᵐ ω ∂d.Q, d.limit ω 0 idx = 0 := by
    apply coupled_zero_of_scalar_observation d hs 0 (fun z => z idx) (continuous_apply idx)
    intro ε hε
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hE : {ω | ε ≤ |Z n ω 0 idx|} = ∅ := by
      ext ω
      simp only [mem_setOf_eq,hi n hn ω,abs_zero,notMem_empty,iff_false,not_le,hε]
    change 0 = M.P {ω | ε ≤ |Z n ω 0 idx|}
    rw [hE,measure_empty]
  have hDa (i : Fin k) : ∀ᵐ ω ∂d.Q, d.driftIntegral 0 ω i = 0 :=
    hZero (ia i) (fun n hn ω => by rw [hA,intervalIntegral.integral_same])
  have hCost : ∀ᵐ ω ∂d.Q, d.runningCost 0 ω = 0 :=
    hZero ic (fun n hn ω => by
      simp only [Z,queueHJBObservation,ic,Fin.append_right,Matrix.cons_val_zero,
        intervalIntegral.integral_same])
  refine ⟨?_,?_,hCost,?_⟩
  · filter_upwards [ae_all_iff.2 hInit] with ω h
    funext i
    exact sub_eq_zero.mp (h i)
  · filter_upwards [ae_all_iff.2 hDa] with ω h
    exact funext h
  have hEq (t : ℝ≥0) (i : Fin k) : ∀ᵐ ω ∂d.Q,
      d.state t ω i-x i-D.r i*d.noise t ω i-d.driftIntegral t ω i = 0 := by
    let φ (z : Fin (k+k+k+2) → ℝ) := z (ix i)-x i-D.r i*z (iw i)-z (ia i)
    have hφ : Continuous φ := by
      unfold φ
      fun_prop
    apply coupled_zero_of_scalar_observation d hs t φ hφ
    intro ε hε
    have hR := he t t.2 (ε/2) (half_pos hε)
    have ht : ∀ᶠ n in atTop, |M.Xhat0 n (X0 n) i-x i| < ε/2 := by
      have h := (continuous_apply i).continuousAt.tendsto.comp hX0
      simpa only [Real.dist_eq,Function.comp_apply] using Metric.tendsto_nhds.1 h (ε/2) (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Eventually.of_forall (fun _ => bot_le)) ?_
    filter_upwards [ht] with n hn
    apply measure_mono
    intro ω hw
    have h : φ (Z n ω t) = e n ω t i + (M.Xhat0 n (X0 n) i-x i) := by
      simp only [φ,hIx,hW,hA,e]
      ring
    change ε ≤ |φ (Z n ω t)| at hw
    rw [h] at hw
    have hE : ε/2 ≤ |e n ω t i| := by linarith [abs_add_le (e n ω t i) (M.Xhat0 n (X0 n) i-x i)]
    refine (ENNReal.ofReal_le_ofReal (hE.trans ?_)).trans
      (le_iSup_of_le (t:ℝ) (le_iSup_of_le (show (t:ℝ) ∈ Icc (0:ℝ) (t:ℝ) from ⟨t.2,le_rfl⟩) le_rfl))
    simpa only [Pi.zero_apply,sub_zero] using
      (Finset.single_le_sum (f := fun j => |e n ω t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hRat : ∀ᵐ ω ∂d.Q, ∀ (q : ℚ) (i : Fin k),
      d.state ((q:ℝ).toNNReal) ω i-x i-D.r i*d.noise ((q:ℝ).toNNReal) ω i-
        d.driftIntegral ((q:ℝ).toNNReal) ω i = 0 :=
    ae_all_iff.2 (fun q => ae_all_iff.2 (hEq (q:ℝ).toNNReal))
  filter_upwards [hRat] with ω hw
  intro t
  funext i
  let g (r : ℝ) :=
    d.state r.toNNReal ω i-x i-D.r i*d.noise r.toNNReal ω i-d.driftIntegral r.toNNReal ω i
  have hc : Continuous g := by
    have hm : Continuous (fun r : ℝ => d.limit ω (r.toNNReal:ℝ)) :=
      (d.limit_cont ω).comp_continuous ((continuous_subtype_val : Continuous (fun x : ℝ≥0 => (x:ℝ))).comp continuous_real_toNNReal) (fun r => r.toNNReal.2)
    exact ((((continuous_apply (ix i)).comp hm).sub continuous_const).sub
      (((continuous_apply (iw i)).comp hm).const_mul _)).sub ((continuous_apply (ia i)).comp hm)
  have hClosed : IsClosed {r : ℝ | g r = 0} := isClosed_eq hc continuous_const
  have hSubset : Set.range (fun q : ℚ => (q:ℝ)) ⊆ {r : ℝ | g r = 0} := by
    rintro r ⟨q,rfl⟩
    exact hw q i
  have hAll := closure_minimal hSubset hClosed
  rw [(Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))).closure_range] at hAll
  have hZ : g t = 0 := hAll (mem_univ (t:ℝ))
  simp only [g,Real.toNNReal_coe] at hZ
  change d.state t ω i = x i+D.r i*d.noise t ω i+d.driftIntegral t ω i
  linarith
