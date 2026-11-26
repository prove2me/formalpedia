-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_arrival_norm_and_modulus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:40:29.843515+00:00
-- url     : https://prove2.me/submissions/443d7756-31be-4635-afd2-80ead252146d

import Theorems.Thm_ManyServerQED_Scheduling_queue_zero_variance_arrivals_uniform_bound
import Theorems.Thm_ManyServerQED_Scheduling_queue_positive_variance_arrivals_uniform_walk_approximation
import Theorems.Thm_ManyServerQED_Scheduling_renewal_epoch_walk_donsker_and_zero_variance
import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus

open Filter Topology Set MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

private theorem approximate_path_modulus {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Q : ℕ → Ω → ℝ → ℝ) (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (T c L : ℝ) (hL : 0 < L) (d : ℕ → ℝ → Set.Icc (0:ℝ) 1)
    (hD : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
      dist (d n s) (d n t) ≤ L* |s-t|)
    (hApprox : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      ε ≤ |Q n ω t - c*Y n ω (d n t)|}) atTop (𝓝 0)) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |Q n ω t|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |Q n ω s-Q n ω t|} ≤ ENNReal.ofReal η := by
  intro ε η hε hη
  let β := ε/3
  let ξ := β/(1+|c|)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  obtain ⟨A,hA,δ,hδ,hYevent⟩ := weak_continuous_path_laws_control_norm_and_modulus
    Y Z hY ξ (η/2) hξ (by positivity)
  let S (n : ℕ) := {ω | ∃ t ∈ Icc (0:ℝ) T, β ≤ |Q n ω t - c*Y n ω (d n t)|}
  let F (n : ℕ) := {ω | A ≤ ‖Y n ω‖ ∨ ∃ s t : Set.Icc (0:ℝ) 1,
    dist s t ≤ δ ∧ ξ ≤ |Y n ω s-Y n ω t|}
  have hSm : ∀ᶠ n in atTop, P (S n) ≤ ENNReal.ofReal (η/2) :=
    ((tendsto_order.1 (hApprox β hβ)).2 _ (ENNReal.ofReal_pos.2 (by positivity))).mono
      (fun _ h => h.le)
  refine ⟨ |c| *A+β,add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg _) hA.le) hβ,
    δ/L,div_pos hδ hL,?_⟩
  filter_upwards [hD,hYevent,hSm] with n hd hf hs
  calc
    _ ≤ P (S n ∪ F n) := by
      apply measure_mono
      intro ω hω
      by_contra hBad
      have hS : ω ∉ S n := fun h => hBad (Or.inl h)
      have hF : ω ∉ F n := fun h => hBad (Or.inr h)
      have hSup : ‖Y n ω‖ < A := lt_of_not_ge (fun h => hF (Or.inl h))
      have herr (t : ℝ) (ht : t ∈ Icc 0 T) : |Q n ω t - c*Y n ω (d n t)| < β :=
        lt_of_not_ge (fun h => hS ⟨t,ht,h⟩)
      rcases hω with ⟨t,ht,htb⟩ | ⟨s,hs',t,ht,hst,hb⟩
      · have hval : |Y n ω (d n t)| ≤ A := by
          rw [← Real.norm_eq_abs]
          exact (ContinuousMap.norm_coe_le_norm _ _).trans hSup.le
        have hQ : |Q n ω t| ≤ |Q n ω t - c*Y n ω (d n t)| + |c*Y n ω (d n t)| := by
          simpa only [sub_add_cancel] using abs_add_le (Q n ω t - c*Y n ω (d n t)) (c*Y n ω (d n t))
        rw [abs_mul] at hQ
        linarith [herr t ht,mul_le_mul_of_nonneg_left hval (abs_nonneg c)]
      · have hu : dist (d n s) (d n t) ≤ δ :=
          (hd s hs' t ht).trans (by
            rw [mul_comm]
            exact (le_div_iff₀ hL).1 hst)
        have hwithin : |Y n ω (d n s)-Y n ω (d n t)| < ξ :=
          lt_of_not_ge (fun h => hF (Or.inr ⟨_,_,hu,h⟩))
        have hscaled : |c| * |Y n ω (d n s)-Y n ω (d n t)| ≤ β := by
          refine (mul_le_mul_of_nonneg_left hwithin.le (abs_nonneg c)).trans ?_
          have hEq : (1+|c|)*ξ = β := by dsimp [ξ]; field_simp
          nlinarith [hξ.le]
        have hQ : |Q n ω s-Q n ω t| ≤ |Q n ω s-c*Y n ω (d n s)| +
            |c| * |Y n ω (d n s)-Y n ω (d n t)| + |Q n ω t-c*Y n ω (d n t)| := by
          let u := Q n ω s-c*Y n ω (d n s)
          let v := c*(Y n ω (d n s)-Y n ω (d n t))
          let w := Q n ω t-c*Y n ω (d n t)
          have eq : Q n ω s-Q n ω t = u+v-w := by dsimp [u,v,w]; ring
          rw [eq]
          calc
            |u+v-w| ≤ |w|+|u+v| := by simpa only [add_comm] using abs_sub (u+v) w
            _ ≤ |w|+(|u|+|v|) := add_le_add_right (abs_add_le _ _) _
            _ = _ := by dsimp [u,v,w]; rw [abs_mul]; ring
        dsimp [β] at hscaled
        have h1 := herr s hs'
        have h2 := herr t ht
        dsimp [β] at h1 h2
        linarith only [h1,h2,hscaled,hQ,hb]
    _ ≤ P (S n) + P (F n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) := add_le_add hs hf
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

set_option maxHeartbeats 1400000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℝ) (hT : 0 ≤ T) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |M.Ahat n ω t i|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |M.Ahat n ω s i-M.Ahat n ω t i|} ≤ ENNReal.ofReal η := by
  let : IsProbabilityMeasure M.P := M.isProb
  have hV : 0 ≤ M.cU2 i := variance_nonneg _ _
  rcases hV.eq_or_lt with hV | hV
  · refine ⟨1,zero_lt_one,1,zero_lt_one,?_⟩
    have h0 : Tendsto (fun n : ℕ => 1/Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h0' := (tendsto_order.1 h0).2 (min 1 (ε/2)) (lt_min zero_lt_one (by positivity))
    filter_upwards [h0'] with n hn
    have hZ := queue_zero_variance_arrivals_uniform_bound M i hV.symm
    refine le_trans (le_of_eq (measure_mono_null ?_ (ae_iff.1 hZ))) zero_le
    intro ω hω hAll
    rcases hω with ⟨t,ht,he⟩ | ⟨s,hs,t,ht,_,he⟩
    · exact not_le_of_gt ((hAll n t ht.1).trans_lt ((lt_min_iff.1 hn).1)) he
    · have h := abs_sub (M.Ahat n ω s i) (M.Ahat n ω t i)
      linarith only [h,he,hAll n s hs.1,hAll n t ht.1,(lt_min_iff.1 hn).2]
  · obtain ⟨J,hJ⟩ := exists_nat_gt ((M.lam i+1)*T+3)
    have hJ0 : 0 < (J:ℝ) := (by nlinarith [M.lam_pos i] : 0 < (M.lam i+1)*T+3).trans hJ
    have hJn : 1 ≤ J := by exact_mod_cast hJ0
    let c := -(Real.sqrt (M.cU2 i)*Real.sqrt (J:ℝ))
    let Y n := walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) (J*n)
    let aN (n : ℕ) := M.lamN n i/n
    let L := (M.lam i+1)/(J:ℝ)
    let d (n : ℕ) (t : ℝ) := projIcc 0 1 zero_le_one (aN n*t/(J:ℝ))
    have hL : 0 < L := div_pos (by linarith [M.lam_pos i]) hJ0
    have hR : Tendsto (fun n : ℕ => J*n) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_id
      change n ≤ J*n
      simpa only [one_mul] using Nat.mul_le_mul_right n hJn
    have hDon := (renewal_epoch_walk_donsker_and_zero_variance M i hB hBc).1 hV
    have hY : TendstoInDistribution Y atTop (brownianPath B) (fun _ => M.P) P' :=
      ⟨fun n => hDon.forall_aemeasurable (J*n),hDon.aemeasurable_limit,hDon.tendsto.comp hR⟩
    have hD : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
        dist (d n s) (d n t) ≤ L*|s-t| := by
      filter_upwards [(tendsto_order.1 (M.lam_lim i)).2 _ (show M.lam i < M.lam i+1 by linarith)]
        with n hn
      have ha : 0 ≤ aN n := div_nonneg (M.lamN_pos n i).le (Nat.cast_nonneg _)
      have hproj (s : ℝ) (hs : s ∈ Icc 0 T) : (d n s : ℝ) = aN n*s/(J:ℝ) := by
        have h0 : 0 ≤ aN n*s/(J:ℝ) := div_nonneg (mul_nonneg ha hs.1) hJ0.le
        have h1 : aN n*s/(J:ℝ) ≤ 1 := by
          apply (div_le_one hJ0).2
          have hb := mul_le_mul (show aN n ≤ M.lam i+1 from hn.le) hs.2 hs.1
            (by linarith [M.lam_pos i] : 0 ≤ M.lam i+1)
          linarith
        simp [d,projIcc,max_eq_right h0,min_eq_right h1]
      intro s hs t ht
      rw [Subtype.dist_eq,Real.dist_eq,hproj s hs,hproj t ht,
        show aN n*s/(J:ℝ)-aN n*t/(J:ℝ) = (aN n/(J:ℝ))*(s-t) by ring,
        abs_mul, abs_of_nonneg (div_nonneg ha hJ0.le)]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn.le hJ0.le) (abs_nonneg _)
    have hApprox (e : ℝ) (he : 0 < e) : Tendsto (fun n => M.P {ω | ∃ t ∈ Icc (0:ℝ) T,
        e ≤ |M.Ahat n ω t i - c*Y n ω (d n t)|}) atTop (𝓝 0) := by
      simpa only [c,neg_mul,sub_neg_eq_add] using
        queue_positive_variance_arrivals_uniform_walk_approximation M i hV P' hB hBc T hT J hJ.le e he
    exact approximate_path_modulus (fun n ω t => M.Ahat n ω t i) Y (brownianPath B)
      hY T c L hL d hD hApprox ε η hε hη
