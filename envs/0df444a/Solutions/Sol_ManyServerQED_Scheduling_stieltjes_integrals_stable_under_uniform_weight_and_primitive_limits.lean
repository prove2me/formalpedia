-- Prove2me | solution 1 for ManyServerQED.Scheduling.stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:44:49.719098+00:00
-- url     : https://prove2.me/submissions/71089d9c-a9fd-4f60-8fe4-e889c4bba99b

import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_ManyServerQED_Scheduling_weighted_lipschitz_path_has_measurable_drift_density
import Theorems.Thm_ManyServerQED_Scheduling_integrated_drift_continuous_weight_limit
import Theorems.Thm_ManyServerQED_Scheduling_right_endpoint_stieltjes_sums_for_cadlag_weight
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling Finset


private theorem right_continuousOn_aestronglyMeasurable (T : ℝ) (hT : 0 ≤ T)
    (v : ℝ → ℝ) (hv : ∀ t ∈ Icc (0:ℝ) T, ContinuousWithinAt v (Ici t) t) :
    AEStronglyMeasurable v (volume.restrict (Icc (0:ℝ) T)) := by
  let f (t : ℝ≥0) (_ : Unit) := v (min (t:ℝ) T)
  have hf (t : ℝ≥0) : Measurable (f t) := measurable_const
  have hr (ω : Unit) (t : ℝ≥0) : ContinuousWithinAt (fun s : ℝ≥0 => f s ω) (Ici t) t := by
    by_cases h : (t:ℝ) ≤ T
    · have he : min (t:ℝ) T = t := min_eq_left h
      let g (s : ℝ≥0) := min (s:ℝ) T
      have hg : Continuous g := continuous_subtype_val.min continuous_const
      have hm : MapsTo g (Ici t) (Ici (min (t:ℝ) T)) :=
        fun s hs => min_le_min_right T (by exact_mod_cast (show t ≤ s from hs))
      have hv' : ContinuousWithinAt v (Ici (g t)) (g t) := by
        dsimp [g]
        rw [he]
        exact hv t ⟨t.2,h⟩
      exact hv'.comp hg.continuousWithinAt hm
    · have hc : ContinuousWithinAt (fun _ : ℝ≥0 => v T) (Ici t) t := continuousWithinAt_const
      apply hc.congr
      · intro s hs
        have hs' : T ≤ (s:ℝ) :=
          (le_of_not_ge h).trans (by exact_mod_cast (show t ≤ s from hs))
        simp only [f,min_eq_right hs']
      · simp only [f,min_eq_right (le_of_not_ge h)]
  have hm := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation f hf hr
  let inc (t : ℝ) : ℝ≥0 × Unit := (t.toNNReal,())
  have hinc : Measurable inc := measurable_id.real_toNNReal.prodMk measurable_const
  have hu : Measurable (fun t : ℝ => v (min (t.toNNReal:ℝ) T)) := hm.comp hinc
  refine hu.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change v (min (t.toNNReal:ℝ) T) = v t
  rw [Real.coe_toNNReal _ ht.1,min_eq_left ht.2]

private noncomputable def rightGrid (T : ℝ) (w A : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m+1), w (T*(j+1:ℕ)/(m+1:ℕ)) *
    (A (T*(j+1:ℕ)/(m+1:ℕ))-A (T*j/(m+1:ℕ)))

set_option maxHeartbeats 2150000 in
theorem solution (T C D : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (v A : ℕ → ℝ → ℝ) (w B b : ℝ → ℝ)
    (hv : ∀ n t, t ∈ Icc (0:ℝ) T → ContinuousWithinAt (v n) (Ici t) t)
    (hvb : ∀ n t, t ∈ Icc (0:ℝ) T → |v n t| ≤ D)
    (hV : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T, |v n t-w t| < ε)
    (hW : ContinuousOn w (Icc (0:ℝ) T))
    (hA : ∀ n s t, s ∈ Icc (0:ℝ) T → t ∈ Icc (0:ℝ) T →
      |A n t-A n s| ≤ C*|t-s|)
    (hAB : ∀ t ∈ Icc (0:ℝ) T, Tendsto (fun n => A n t) atTop (𝓝 (B t)))
    (hB : ∀ t ∈ Icc (0:ℝ) T, (∫ s in (0:ℝ)..t,b s) = B t-B 0)
    (hb : IntervalIntegrable b volume 0 T) (hbb : ∀ t ∈ Icc (0:ℝ) T, |b t| ≤ C) :
    ∃ z : ℕ → ℝ, (∀ n, Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
      v n (T*(j+1:ℕ)/(m+1:ℕ)) *
      (A n (T*(j+1:ℕ)/(m+1:ℕ))-A n (T*j/(m+1:ℕ)))) atTop (𝓝 (z n))) ∧
      Tendsto z atTop (𝓝 (∫ s in (0:ℝ)..T,w s*b s)) := by
  have hA' (n : ℕ) : ∃ a : ℝ → ℝ, Measurable a ∧ (∀ r, |a r| ≤ C) ∧
      ∀ t ∈ Icc (0:ℝ) T, (∫ s in (0:ℝ)..t,a s) = A n t-A n 0 := by
    let clip (x : ℝ) := min (max x 0) T
    have hc : LipschitzWith 1 clip := by
      have hi : LipschitzWith 1 (id : ℝ → ℝ) := LipschitzWith.id
      have hc := (hi.max (LipschitzWith.const (0:ℝ))).min (LipschitzWith.const T)
      simpa only [id_eq,max_eq_left (zero_le (a := (1:ℝ≥0)))] using hc
    have hF (t : ℝ) : clip t ∈ Icc (0:ℝ) T := ⟨le_min (le_max_right _ _) hT,min_le_right _ _⟩
    have hE (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : clip t = t := by
      dsimp [clip]
      rw [max_eq_left ht.1,min_eq_left ht.2]
    have hR (s t : ℝ) : |A n (clip t)-A n (clip s)| ≤ C*|t-s| := by
      have h := hc.dist_le_mul t s
      rw [NNReal.coe_one,one_mul,Real.dist_eq,Real.dist_eq] at h
      exact (hA n (clip s) (clip t) (hF s) (hF t)).trans (mul_le_mul_of_nonneg_left h hC)
    let data (ω : Unit) (t : ℝ) (_ : Fin 1) := A n (clip t)
    have hm : Measurable (fun z : Unit × ℝ => data z.1 z.2) := by
      apply measurable_pi_lambda
      intro i
      have hc : Continuous (fun t => A n (clip t)) := by
        apply (LipschitzWith.of_dist_le_mul (K := C.toNNReal) ?_).continuous
        intro s t
        rw [Real.coe_toNNReal _ hC,Real.dist_eq,Real.dist_eq]
        exact hR t s
      exact hc.measurable.comp measurable_snd
    obtain ⟨a,hM,hBound,hEq⟩ := weighted_lipschitz_path_has_measurable_drift_density data
      (fun _ _ => C) hm measurable_const (fun _ => continuous_const) (fun _ _ => hC)
      (fun ω s t K hs ht h => by
        have hh : C ≤ K := h s (left_mem_uIcc (a := s) (b := t))
        apply (pi_norm_le_iff_of_nonneg (mul_nonneg (hC.trans hh) (abs_nonneg _))).2
        intro i
        rw [Pi.sub_apply,Real.norm_eq_abs]
        exact (hR s t).trans (mul_le_mul_of_nonneg_right hh (abs_nonneg _)))
    let a' (t : ℝ) := a () t 0
    have hm' : Measurable (fun t => a () t) := hM.comp (measurable_const.prodMk measurable_id)
    have ha' : Measurable a' := (measurable_pi_apply 0).comp hm'
    have hb' (t : ℝ) : |a' t| ≤ C := by
      exact (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a () t) 0 :
        |a' t| ≤ ‖a () t‖).trans (hBound () t)
    have hInt (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable (a ()) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht enorm_ne_top]
      apply Measure.integrableOn_of_bounded (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
        hm'.aestronglyMeasurable
      exact Eventually.of_forall (hBound ())
    refine ⟨a',ha',hb',?_⟩
    intro t ht
    have hh := congrFun (hEq () t ht.1) (0 : Fin 1)
    let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)
    have hp := proj.intervalIntegral_comp_comm (hInt t ht.1)
    change (∫ s in (0:ℝ)..t, a' s) = (∫ s in (0:ℝ)..t,a () s) 0 at hp
    rw [← hp] at hh
    simpa only [data,Pi.sub_apply,hE t ht,hE 0 ⟨le_rfl,hT⟩] using hh
  choose a hAm hAc hAp using hA'
  have hInt (n : ℕ) : IntervalIntegrable (a n) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT enorm_ne_top]
    apply Measure.integrableOn_of_bounded (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
      (hAm n).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hAc n t)
  let z (n : ℕ) := ∫ t in (0:ℝ)..T,v n t*a n t
  refine ⟨z,?_,?_⟩
  · intro n
    have H := right_endpoint_stieltjes_sums_for_cadlag_weight T C D hT hC hD
      (v n) (a n) (hv n) (hvb n) (hInt n) (fun t _ => hAc n t)
    have hR (m : ℕ) : (∑ j ∈ range (m+1), v n (T*(j+1:ℕ)/(m+1:ℕ)) *
        ((∫ s in (0:ℝ)..T*(j+1:ℕ)/(m+1:ℕ),a n s)-
         (∫ s in (0:ℝ)..T*j/(m+1:ℕ),a n s))) = rightGrid T (v n) (A n) m := by
      unfold rightGrid
      apply Finset.sum_congr rfl
      intro j hj
      have hm (l : ℕ) (hl : l ≤ m+1) : T*l/(m+1:ℕ) ∈ Icc (0:ℝ) T := by
        refine ⟨by positivity, (div_le_iff₀ (by positivity)).2 ?_⟩
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hT
      rw [hAp n _ (hm _ (mem_range.1 hj)),hAp n _ (hm _ ((mem_range.1 hj).le))]
      ring
    exact H.congr' (Eventually.of_forall hR)
  have hbMeas (n : ℕ) : AEStronglyMeasurable (v n) (volume.restrict (Icc 0 T)) :=
    right_continuousOn_aestronglyMeasurable T hT (v n) (hv n)
  have hIntV (n : ℕ) : IntervalIntegrable (fun t => v n t*a n t) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT enorm_ne_top]
    letI : IsFiniteMeasure (volume.restrict (Icc 0 T)) :=
      isFiniteMeasure_restrict.2 (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
    refine ⟨(hbMeas n).mul (hAm n).aestronglyMeasurable,HasFiniteIntegral.of_bounded (C := D*C) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hvb n t ht) (hAc n t) (abs_nonneg _) hD
  have hIntW : IntervalIntegrable (fun t => w t*b t) volume 0 T :=
    hb.continuousOn_mul (by simpa only [uIcc_of_le hT] using hW)
  have hP (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) :
      Tendsto (fun n => ∫ s in (0:ℝ)..t,a n s) atTop (𝓝 (B t-B 0)) := by
    simp_rw [hAp _ _ ht]
    exact (hAB t ht).sub (hAB 0 ⟨le_rfl,hT⟩)
  obtain ⟨x,hx,hx'⟩ := integrated_drift_continuous_weight_limit T C hT hC
    v a w (fun t => B t-B 0) hW hV hInt (fun n t _ => hAc n t) hIntV hP
  obtain ⟨y,hy,hy'⟩ := integrated_drift_continuous_weight_limit T C hT hC
    (fun _ => w) (fun _ => b) w (fun t => B t-B 0) hW
    (fun ε hε => Eventually.of_forall fun n t _ => by change |w t-w t| < ε; rwa [sub_self,abs_zero])
    (fun _ => hb) (fun _ => hbb) (fun _ => hIntW)
    (fun t ht => hB t ht ▸ tendsto_const_nhds)
  have hy0 : y = ∫ t in (0:ℝ)..T,w t*b t := tendsto_nhds_unique hy tendsto_const_nhds
  rw [← hy0,← tendsto_nhds_unique hx' hy']
  exact hx
