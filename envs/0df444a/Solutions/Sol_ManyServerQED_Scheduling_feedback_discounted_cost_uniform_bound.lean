-- Prove2me | solution 1 for ManyServerQED.Scheduling.feedback_discounted_cost_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:32:48.529811+00:00
-- url     : https://prove2.me/submissions/739f1856-b108-4573-b3a9-ada0062632df

import Theorems.Thm_ManyServerQED_Scheduling_lemma_3
import Theorems.Thm_ManyServerQED_Scheduling_feedback_state_measurable
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal

private theorem discounted_poly_integrable (C p γ : ℝ) (hp : 0 ≤ p) (hγ : 0 < γ) :
    IntegrableOn (fun t : ℝ => C * (Real.exp (-γ * t) * (1 + t ^ p))) (Ioi 0) := by
  have hExp : IntegrableOn (fun t : ℝ => Real.exp (-γ * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hγ) 0
  have hProd : IntegrableOn (fun t : ℝ => Real.exp (-γ * t) * t ^ p) (Ioi 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p) (b := γ) (by linarith)
        (by norm_num) hγ)
  change Integrable _ (volume.restrict (Ioi 0 : Set ℝ))
  simpa only [Pi.add_apply, mul_add, mul_one] using (hExp.add hProd).const_mul C

private theorem polynomial_discounted_cost_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℕ → Ω → ℝ → ℝ≥0∞) (hc : ∀ n, Measurable (Function.uncurry (c n)))
    (C p γ : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hγ : 0 < γ)
    (N : ℕ) (hBound : ∀ n ≥ N, ∀ t > 0, (∫⁻ ω, c n ω t ∂P) ≤ ENNReal.ofReal (C * (1 + t ^ p))) :
    (∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n ≥ N, (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t
      ∂volume ∂P) ≤ K) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℕ, ∀ n ≥ N,
      (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t ∂volume ∂P) < ε) := by
  let H (t : ℝ) := ENNReal.ofReal (C * (Real.exp (-γ * t) * (1 + t ^ p)))
  let μ : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity H
  have hMass : μ univ < ⊤ := by
    rw [show μ univ = ∫⁻ t in Ioi (0 : ℝ), H t ∂volume by
      simp only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]]
    let f (t : ℝ) := C * (Real.exp (-γ * t) * (1 + t ^ p))
    have hi : Integrable f (volume.restrict (Ioi 0)) := discounted_poly_integrable C p γ hp hγ
    change (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) ∂volume) < ⊤
    exact (lintegral_ofReal_le_lintegral_enorm f).trans_lt hi.hasFiniteIntegral
  have htail (T : ℕ) : μ (Ioi (T : ℝ)) = ∫⁻ t in Ioi (T : ℝ), H t ∂volume := by
    change ((volume.restrict (Ioi (0 : ℝ))).withDensity H) _ = _
    rw [withDensity_apply H measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hsub : Ioi (T : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (Nat.cast_nonneg T)
    simp only [inter_eq_left.2 hsub]
  have hbound (n : ℕ) (hn : N ≤ n) (T : ℕ) :
      (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t ∂volume ∂P) ≤
        μ (Ioi (T : ℝ)) := by
    let u (ω : Ω) (t : ℝ) := ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t
    have hW : Measurable (Function.uncurry u) := by
      exact ((measurable_snd.const_mul (-γ)).exp.ennreal_ofReal).mul (hc n)
    change (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), u ω t ∂volume ∂P) ≤ μ (Ioi (T : ℝ))
    rw [lintegral_lintegral_swap hW.aemeasurable, htail]
    apply setLIntegral_mono_ae' measurableSet_Ioi
    refine ae_of_all _ (fun t ht => ?_)
    have ht0 : 0 < t := (Nat.cast_nonneg T).trans_lt ht
    have hr : 0 ≤ C * (1 + t ^ p) := mul_nonneg hC (add_nonneg zero_le_one (Real.rpow_nonneg ht0.le _))
    dsimp [u, H]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (hBound n hn t ht0) _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    ring
  have hμt : Tendsto (fun T : ℕ => μ (Ioi (T : ℝ))) atTop (𝓝 0) := by
    have hm : Antitone (fun T : ℕ => Ioi (T : ℝ)) := fun a b h => Ioi_subset_Ioi (by exact_mod_cast h)
    have he : (⋂ T : ℕ, Ioi (T : ℝ)) = (∅ : Set ℝ) := by
      apply eq_empty_iff_forall_notMem.2
      intro t ht
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact (not_lt_of_ge hn.le) (mem_iInter.1 ht n)
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Ioi.nullMeasurableSet)
      hm ⟨0, ne_top_of_le_ne_top hMass.ne (measure_mono (subset_univ _))⟩
    rwa [he, measure_empty] at h
  refine ⟨⟨μ univ, hMass, fun n hn => ?_⟩, fun ε hε => ?_⟩
  · have hb := (hbound n hn 0).trans (measure_mono (subset_univ _))
    simpa only [Nat.cast_zero] using hb
  · obtain ⟨T, hT⟩ := ((tendsto_order.1 hμt).2 ε hε).exists
    exact ⟨T, fun n hn => (hbound n hn T).trans_lt hT⟩

open scoped NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem arrival_prefix_index {e : ℕ → ℝ} {s : ℝ}
    (h0 : e 0 ≤ s) (hm : ∃ m, s < e m) :
    ∃ j : ℕ, e j ≤ s ∧ s < e (j + 1) := by
  let b := Nat.find hm
  have hb : s < e b := Nat.find_spec hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  exact ⟨j, le_of_not_gt (Nat.find_min hm hj_lt), hsucc ▸ (show s < e b from hb)⟩

private theorem renewal_eq_of_bracket {e : ℕ → ℝ} (he : Monotone e) {s : ℝ} {j : ℕ}
    (hj : e j ≤ s) (hj_succ : s < e (j + 1)) : renewalCount e s = j := by
  unfold renewalCount
  refine le_antisymm (iSup_le fun r => iSup_le fun hr => ?_) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have h : r ≤ j := by
    by_contra! hjr
    exact (not_lt_of_ge hr) (hj_succ.trans_le (he hjr))
  exact_mod_cast h

private theorem arrival_right_continuous {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (M.A n i ω) (Set.Ici t) t := by
  let e := M.arrivalEpoch n i ω
  let r := M.lamN n i
  have hr : 0 < r := M.lamN_pos n i
  have he (j : ℕ) : e j = partialSum (fun m => M.U i m ω) j / r := by
    simp [e, r, SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  have hmono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hj := M.U_pos i (j + 1) ω (by omega)
    rw [he, he]
    apply (div_lt_div_iff_of_pos_right hr).2
    unfold partialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
    linarith
  have hz : e 0 = 0 := by simp [he, partialSum]
  have hcross : ∃ m : ℕ, t < e m := by
    have hh := ((tendsto_atTop.1 (M.U_finite i ω)) (t * r + 1)).exists
    obtain ⟨m, hm⟩ := hh
    refine ⟨m, ?_⟩
    rw [he, lt_div_iff₀ hr]
    linarith
  obtain ⟨j, hj, hsucc⟩ := arrival_prefix_index (hz ▸ ht) hcross
  have hc (s : ℝ) (hs : t ≤ s) (hs' : s < e (j + 1)) : M.A n i ω s = j := by
    simp [SystemSequence.A, ← show e = M.arrivalEpoch n i ω from rfl,
      renewal_eq_of_bracket hmono.monotone (hj.trans hs) hs']
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [self_mem_nhdsWithin (s := Set.Ici t),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsucc)] with s hs hsu
  exact (hc s hs hsu).trans (hc t le_rfl hsucc).symm

private theorem clock_monotone {v : ℝ → ℝ}
    (hi : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t)
    (hv : ∀ t, 0 ≤ t → 0 ≤ v t) :
    MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Ici 0) := by
  intro a ha b hb hab
  have h := intervalIntegral.integral_add_adjacent_intervals (hi a ha)
    ((hi a ha).symm.trans (hi b hb))
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab (fun s hs => hv s (ha.trans hs.1))
  linarith

private theorem clock_continuous_right {v : ℝ → ℝ}
    (hi : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Ici t) t := by
  have htop : t < t + 1 := by linarith
  have hh : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Icc 0 (t + 1)) := by
    simpa only [Set.uIcc_of_le (show 0 ≤ t + 1 by linarith)] using
      intervalIntegral.continuousOn_primitive_interval' (hi (t + 1) (by linarith))
        (Set.left_mem_uIcc (a := (0 : ℝ)) (b := t + 1))
  exact (hh t ⟨ht, htop.le⟩).mono_of_mem_nhdsWithin (by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ici t),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htop)] with s hs hu
    exact ⟨ht.trans hs, hu.le⟩)

private theorem state_right_continuous {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (h : M.IsControlled n X0 X Ψ) (ω : Ω) (i : Fin k) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => X ω s i) (Set.Ici t) t := by
  have hiR (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).2
  have hiS (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).1
  have hRmono := clock_monotone hiR (fun s hs => h.phi_nonneg ω s i hs)
  have hSmono := clock_monotone hiS (fun s hs => h.psi_nonneg ω s i hs)
  have hR0 : 0 ≤ queueTime X Ψ ω i t :=
    intervalIntegral.integral_nonneg ht (fun s hs => h.phi_nonneg ω s i hs.1)
  have hS0 : 0 ≤ busyTime Ψ ω i t :=
    intervalIntegral.integral_nonneg ht (fun s hs => h.psi_nonneg ω s i hs.1)
  have hcR : ContinuousWithinAt (fun s => M.R n i ω (queueTime X Ψ ω i s)) (Set.Ici t) t :=
    ((M.R_poisson n i).cadlag ω).1 _ hR0 |>.comp (clock_continuous_right hiR t ht)
      (fun s hs => hRmono ht (ht.trans hs) hs)
  have hcS : ContinuousWithinAt (fun s => M.S n i ω (busyTime Ψ ω i s)) (Set.Ici t) t :=
    ((M.S_poisson n i).cadlag ω).1 _ hS0 |>.comp (clock_continuous_right hiS t ht)
      (fun s hs => hSmono ht (ht.trans hs) hs)
  have hh : ContinuousWithinAt
      (fun s => (X0 i : ℝ) + M.A n i ω s - M.R n i ω (queueTime X Ψ ω i s) -
        M.S n i ω (busyTime Ψ ω i s)) (Set.Ici t) t :=
    ((continuousWithinAt_const.add (arrival_right_continuous M n i ω t ht)).sub hcR).sub hcS
  exact hh.congr (fun s hs => h.eq7 ω s i (ht.trans hs)) (h.eq7 ω t i ht)


section
variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

private theorem sum_Xhat (M : SystemSequence Ω k) (n : ℕ) (X : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ) :
    ∑ j, M.Xhat n X ω t j = (∑ j, X ω t j - n) / Real.sqrt n := by
  unfold SystemSequence.Xhat
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, M.rho i = 1 := M.sum_rho
  rw [this, one_mul]

private theorem integrand_eq (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (n : ℕ) (hn : 1 ≤ n) (u0 : Fin k → ℝ) (X Ψ : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ)
    (hnn : ∀ i, 0 ≤ X ω t i - Ψ ω t i)
    (hwc : max (∑ i, X ω t i - n) 0 = ∑ i, (X ω t i - Ψ ω t i)) :
    Lt (Phihat n X Ψ ω t) (M.Psihat n Ψ ω t) =
      costOfTilde Lt (M.Xhat n X ω t) (uProc n u0 X Ψ ω t) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hPhi : Phihat n X Ψ ω t = max (∑ j, M.Xhat n X ω t j) 0 • uProc n u0 X Ψ ω t := by
    rw [sum_Xhat]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Phihat, uProc]
    split_ifs with hpos
    · rw [max_eq_left (div_nonneg hpos.le hsn.le)]
      field_simp
    · push Not at hpos
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hpos hsn.le), zero_mul]
      have h0 : ∑ i, (X ω t i - Ψ ω t i) = 0 := by rw [← hwc, max_eq_right hpos]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)] at h0
      rw [h0 i (Finset.mem_univ _), zero_div]
  unfold costOfTilde
  rw [← hPhi]
  congr 1
  funext i
  simp only [SystemSequence.Psihat, Pi.sub_apply, SystemSequence.Xhat, Phihat]
  ring


end

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Y : ℕ → Ω → ℝ → Fin k → ℕ) (F : ℕ → (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ n v i, F n v i ≤ v i)
    (hPol : ∀ n, 1 ≤ n →
      let X : Ω → ℝ → Fin k → ℝ := fun ω t i => (Y n ω t i : ℝ)
      let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F n (Y n ω t) i : ℝ)
      M.IsSCP n (X0 n) X Ψ ∧ M.IsAdmissible n X Ψ ∧ IsWorkConserving n X Ψ) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ᶠ n in atTop,
      M.queueCostL (costOfTilde Lt) γ n u0 (fun ω t i => (Y n ω t i : ℝ))
        (fun ω t i => (F n (Y n ω t) i : ℝ)) ≤ K := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let X (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : ℝ := Y n ω t i
  let Ψ (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : ℝ := F n (Y n ω t) i
  have hC (n : ℕ) (hn : 1 ≤ n) : M.IsControlled n (X0 n) (X n) (Ψ n) :=
    (hPol n hn).1.controlled
  have hY (n : ℕ) (hn : 1 ≤ n) : Measurable (fun z : Ω × ℝ => Y n z.1 z.2.toNNReal) := by
    apply measurable_pi_lambda
    intro i
    have hj : ∀ (t : ℝ≥0), Measurable (fun ω => X n ω t i) := fun t =>
      (measurable_of_countable (fun y : Fin k → ℕ => (y i : ℝ))).comp
        (feedback_state_measurable M n (X0 n) (F n) (hF n) (Y n) (hC n hn) t t.2)
    have hr (ω : Ω) (t : ℝ≥0) : ContinuousWithinAt (fun s : ℝ≥0 => X n ω s i) (Ici t) t :=
      ((state_right_continuous M n (X0 n) (X n) (Ψ n) (hC n hn) ω i t t.2).comp
        continuous_subtype_val.continuousWithinAt) (fun _ hs => hs)
    have hjoint := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      (fun t ω => X n ω t i) hj hr
    have hm := hjoint.comp (measurable_snd.real_toNNReal.prodMk measurable_fst)
    simpa only [Function.comp_def, X, Nat.floor_natCast] using hm.nat_floor
  let g (n : ℕ) (ω : Ω) (t : ℝ) := if 1 ≤ n then ENNReal.ofReal
    (Lt (Phihat n (X n) (Ψ n) ω t.toNNReal) (M.Psihat n (Ψ n) ω t.toNNReal)) else 0
  have hg (n : ℕ) : Measurable (Function.uncurry (g n)) := by
    by_cases hn : 1 ≤ n
    · simp only [g, if_pos hn]
      have hΦ : Measurable (fun z : Ω × ℝ => Phihat n (X n) (Ψ n) z.1 z.2.toNNReal) :=
        (measurable_of_countable (fun y : Fin k → ℕ => fun i =>
          ((y i : ℝ) - (F n y i : ℝ)) / Real.sqrt n)).comp (hY n hn)
      have hΨ : Measurable (fun z : Ω × ℝ => M.Psihat n (Ψ n) z.1 z.2.toNNReal) :=
        (measurable_of_countable (fun y : Fin k → ℕ => fun i =>
          ((F n y i : ℝ) - M.rho i * n) / Real.sqrt n)).comp (hY n hn)
      exact (hA2.tilde_cont.measurable.comp (hΦ.prodMk hΨ)).ennreal_ofReal
    · simp only [g, if_neg hn]
      exact measurable_const
  have hGt (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      g n ω t = ENNReal.ofReal (costOfTilde Lt (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t)) := by
    dsimp only [g]
    rw [Real.coe_toNNReal _ ht, integrand_eq M Lt n hn u0 (X n) (Ψ n) ω t
      (fun i => (hC n hn).phi_nonneg ω t i ht) ((hPol n hn).2.2 ω t ht), if_pos hn]
  have hUm (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      uProc n u0 (X n) (Ψ n) ω t ∈ stdSimplex ℝ (Fin k) := by
    unfold uProc
    split_ifs with h
    · refine ⟨fun i => div_nonneg ((hC n hn).phi_nonneg ω t i ht) h.le, ?_⟩
      rw [← Finset.sum_div, ← (hPol n hn).2.2 ω t ht, max_eq_left h.le, div_self h.ne']
    · exact hu0
  obtain ⟨a, ha, hA⟩ := hA2.cost.growth
  obtain ⟨c, m, hMom⟩ := lemma_3 M mL mU hA3
  obtain ⟨N, hN⟩ := hMom x X0 hX0 X Ψ hPol
  let b := max c 0 * (1 + l1norm x ^ m)
  have hx0 : 0 ≤ l1norm x := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  have hb : 0 ≤ b := mul_nonneg (le_max_right c 0) (by positivity)
  have hU : 0 ≤ mU := hA3.1.trans' (by norm_num)
  have hV (n : ℕ) (ω : Ω) (t : ℝ) : 0 ≤ l1norm (M.Xhat n (X n) ω t) :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hExp (n : ℕ) (hn : max N 1 ≤ n) (t : ℝ) (ht : 0 < t) :
      (∫⁻ ω, g n ω t ∂M.P) ≤ ENNReal.ofReal ((a * (2 + b)) * (1 + t ^ (m : ℝ))) := by
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hNn : N ≤ n := (le_max_left _ _).trans hn
    let v (ω : Ω) := ENNReal.ofReal (l1norm (M.Xhat n (X n) ω t)) ^ mU
    have hpoint (ω : Ω) : g n ω t ≤ ENNReal.ofReal a * (2 + v ω) := by
      rw [hGt n hn1 ω t ht.le]
      let z := l1norm (M.Xhat n (X n) ω t)
      have hz : 0 ≤ z := hV n ω t
      have hpow : z ^ mL ≤ 1 + z ^ mU := by
        rcases le_total z 1 with h | h
        · exact (Real.rpow_le_one hz h hA2.cost.mL_nonneg).trans (le_add_of_nonneg_right (Real.rpow_nonneg hz _))
        · exact (Real.rpow_le_rpow_of_exponent_le h hA3.2.1.le).trans (le_add_of_nonneg_left zero_le_one)
      calc
        _ ≤ ENNReal.ofReal (a * (1 + z ^ mL)) := ENNReal.ofReal_le_ofReal (hA _ (hUm n hn1 ω t ht.le) _)
        _ ≤ ENNReal.ofReal (a * (2 + z ^ mU)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) ha.le)
        _ = _ := by
          rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add (by norm_num : 0 ≤ (2 : ℝ)) (Real.rpow_nonneg hz _),
            ← ENNReal.ofReal_rpow_of_nonneg hz hU]
          simp only [v, z, ENNReal.ofReal_ofNat]
    have htM : (∫⁻ ω, v ω ∂M.P) ≤ ENNReal.ofReal (b * (1 + t ^ m)) := by
      refine (hN n hNn t ht.le).trans (ENNReal.ofReal_le_ofReal ?_)
      unfold b
      gcongr
      exact le_max_left _ _
    have hw : ENNReal.ofReal a * (2 + ENNReal.ofReal (b * (1 + t ^ m))) =
        ENNReal.ofReal (a * (2 + b * (1 + t ^ m))) := by
      rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add (by norm_num : 0 ≤ (2 : ℝ))
        (mul_nonneg hb (by positivity)), ENNReal.ofReal_ofNat]
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal a * (2 + v ω) ∂M.P := lintegral_mono hpoint
      _ = ENNReal.ofReal a * (2 + ∫⁻ ω, v ω ∂M.P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal a * (2 + ENNReal.ofReal (b * (1 + t ^ m))) := by gcongr
      _ = ENNReal.ofReal (a * (2 + b * (1 + t ^ m))) := hw
      _ ≤ _ := by
        rw [Real.rpow_natCast]
        apply ENNReal.ofReal_le_ofReal
        have hh : 0 ≤ t ^ m := pow_nonneg ht.le _
        nlinarith [mul_nonneg ha.le hh]
  obtain ⟨⟨K, hK, hB⟩, _⟩ := polynomial_discounted_cost_bound M.P g hg (a * (2 + b)) (m : ℝ)
    γ (by positivity) (Nat.cast_nonneg _) hγ (max N 1) hExp
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  refine le_of_eq ?_ |>.trans (hB n hn)
  unfold SystemSequence.queueCostL
  congr 1
  funext ω
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [hGt n hn1 ω t ht.le, ENNReal.ofReal_mul (Real.exp_nonneg _)]
