-- Prove2me | solution 1 for ManyServerQED.Scheduling.uniform_path_approximation_transfers_norm_and_modulus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:40:29.845418+00:00
-- url     : https://prove2.me/submissions/6c797a92-c280-4e47-bbd0-bc08762e9834

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus

open Filter Topology Set MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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
