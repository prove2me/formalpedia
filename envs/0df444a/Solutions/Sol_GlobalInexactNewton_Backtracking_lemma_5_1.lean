-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:15:19.572135+00:00
-- url     : https://prove2.me/submissions/83759112-9ee9-406c-8aa6-fb14b00967a9

import Init
import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

open Filter Topology
open GlobalInexactNewton.Backtracking
namespace NewtonTrials

theorem levels (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ) (n : ℕ)
    (hmem : ∀ j < n, θ j ∈ Set.Icc θmin θmax) :
    ηbar ≤ trialLevel ηbar θ n ∧ trialLevel ηbar θ n < 1 := by
  induction n with
  | zero => exact ⟨le_rfl,hη.2⟩
  | succ n ih =>
    obtain ⟨hl,hu⟩ := ih (fun j hj => hmem j (Nat.lt_succ_of_lt hj))
    have ht := hmem n (Nat.lt_succ_self n)
    have hp := mul_le_mul_of_nonneg_right (ht.2.trans hθ.2.2.le) (sub_nonneg.mpr hu.le)
    have hpos := mul_pos (hθ.1.trans_le ht.1) (sub_pos.mpr hu)
    simp only [trialLevel]
    constructor <;> nlinarith

theorem gap_bound (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ)
    (hmem : ∀ j, θ j ∈ Set.Icc θmin θmax) (n : ℕ) :
    0 ≤ 1-trialLevel ηbar θ n ∧ 1-trialLevel ηbar θ n ≤ θmax^n*(1-ηbar) := by
  have hl := levels ηbar θmin θmax hη hθ θ n (fun j _ => hmem j)
  refine ⟨by linarith,?_⟩
  induction n with
  | zero => simp [trialLevel]
  | succ n ih =>
    have hn := levels ηbar θmin θmax hη hθ θ n (fun j _ => hmem j)
    have ht := hmem n
    have hx : 0 < θmax := lt_trans hθ.1 hθ.2.1
    have hm := mul_le_mul_of_nonneg_left (ih hn) hx.le
    have hb := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hn.2.le)
    simp only [trialLevel,pow_succ]
    nlinarith

theorem gap_tendsto (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ)
    (hmem : ∀ j, θ j ∈ Set.Icc θmin θmax) :
    Tendsto (fun n => 1-trialLevel ηbar θ n) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (lt_trans hθ.1 hθ.2.1)) hθ.2.2).mul_const (1-ηbar)
  apply squeeze_zero (fun n => (gap_bound ηbar θmin θmax hη hθ θ hmem n).1)
    (fun n => (gap_bound ηbar θmin θmax hη hθ θ hmem n).2)
  simpa using hp

#print axioms gap_tendsto
end NewtonTrials

open Filter Topology
open GlobalInexactNewton.Backtracking
namespace NewtonLine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gamma_pos (F : E → E) (x : E) (ηbar : ℝ) (hη : ηbar < 1)
    (σ : ℝ → E) (hi : InexactNewtonCond F x (σ ηbar) ηbar) (hF : F x ≠ 0)
    (Γ : ℝ) (hg : ‖σ ηbar‖ ≤ Γ*(1-ηbar)*‖F x‖) : 0 < Γ := by
  have hn : 0 < ‖F x‖ := norm_pos_iff.mpr hF
  have hs : σ ηbar ≠ 0 := by
    intro hz
    simp only [InexactNewtonCond,hz,map_zero,add_zero] at hi
    nlinarith
  by_contra! hΓ
  have hp := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hΓ (by linarith : 0 ≤ 1-ηbar)) hn.le
  have hsn := norm_pos_iff.mpr hs
  linarith

theorem remainder (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ,
      ‖F y-F x-fderiv ℝ F x (y-x)‖ ≤ ε*‖y-x‖ := by
  have hd := (hF.differentiable one_ne_zero x).hasFDerivAt.isLittleO.def hε
  obtain ⟨δ,hδ,h⟩ := Metric.eventually_nhds_iff.mp hd
  exact ⟨δ,hδ,fun y hy => h (Metric.mem_ball.mp hy)⟩

theorem small_accept (F : E → E) (x : E) (t Γ η δ : ℝ) (ht : t < 1) (hΓ : 0 < Γ)
    (s : E) (hi : InexactNewtonCond F x s η)
    (hg : ‖s‖ ≤ Γ*(1-η)*‖F x‖)
    (hsmall : Γ*(1-η)*‖F x‖ < δ)
    (hrem : ∀ y ∈ Metric.ball x δ,
      ‖F y-F x-fderiv ℝ F x (y-x)‖ ≤ (1-t)/Γ*‖y-x‖) :
    SuffDecrease F t x s η := by
  have hnear : x+s ∈ Metric.ball x δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left] using hg.trans_lt hsmall
  have hr := hrem (x+s) hnear
  simp only [add_sub_cancel_left] at hr
  have heps : 0 ≤ (1-t)/Γ := div_nonneg (sub_nonneg.mpr ht.le) hΓ.le
  have hm := mul_le_mul_of_nonneg_left hg heps
  have he : (1-t)/Γ*(Γ*(1-η)*‖F x‖) = (1-t)*(1-η)*‖F x‖ := by
    field_simp [ne_of_gt hΓ]
  rw [he] at hm
  have htri : ‖F (x+s)‖ ≤ ‖F x+fderiv ℝ F x s‖ + ‖F (x+s)-F x-fderiv ℝ F x s‖ := by
    have h := norm_add_le (F x+fderiv ℝ F x s) (F (x+s)-F x-fderiv ℝ F x s)
    convert h using 1 <;> congr 1 <;> abel
  unfold InexactNewtonCond at hi
  unfold SuffDecrease
  nlinarith

#print axioms remainder
#print axioms small_accept
end NewtonLine

open Filter Topology
open GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), p. 408, Lemma 5.1, for one iteration of the while-loop shared by
Algorithms MR and TL. Data: `t ∈ (0,1)`, `0 < θ_min < θ_max < 1`, the current iterate `x_k`, an
initial level `η̄_k ∈ [0,1)`, a curve `σ_k` with (5.1) on `[η̄_k, 1]`, and an arbitrary choice of
factors `θ_j ∈ [θ_min, θ_max]`. If `F(x_k) ≠ 0` and `Γ` satisfies (5.3)
`‖σ_k(η)‖ ≤ Γ (1 - η) ‖F(x_k)‖` on `[η̄_k, 1]`, then the while-loop terminates (some trial passes (2.2)
after all earlier trials failed), and at termination (5.4)
`1 - η_k ≥ min {1 - η̄_k, θ_min δ / (Γ ‖F(x_k)‖)}` for every `δ > 0` with (5.5)
`‖F(x) - F(x_k) - F'(x_k)(x - x_k)‖ ≤ ((1 - t)/Γ) ‖x - x_k‖` on `N_δ(x_k)`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t θmin θmax : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1)
    (xk : E) (ηbar : ℝ) (hηbar : ηbar ∈ Set.Ico (0 : ℝ) 1) (σ : ℝ → E)
    (hσ : ∀ η ∈ Set.Icc ηbar 1, InexactNewtonCond F xk (σ η) η)
    (hFxk : F xk ≠ 0) (Γ : ℝ) (hΓ : ∀ η ∈ Set.Icc ηbar 1, ‖σ η‖ ≤ Γ * (1 - η) * ‖F xk‖)
    (θ : ℕ → ℝ) (hθmem : ∀ j, θ j ∈ Set.Icc θmin θmax) :
    (∃ m : ℕ, (∀ j < m, ¬ SuffDecrease F t xk (σ (trialLevel ηbar θ j)) (trialLevel ηbar θ j)) ∧
        SuffDecrease F t xk (σ (trialLevel ηbar θ m)) (trialLevel ηbar θ m)) ∧
      ∀ m : ℕ, (∀ j < m, ¬ SuffDecrease F t xk (σ (trialLevel ηbar θ j)) (trialLevel ηbar θ j)) →
        SuffDecrease F t xk (σ (trialLevel ηbar θ m)) (trialLevel ηbar θ m) →
        ∀ δ > 0, (∀ y ∈ Metric.ball xk δ,
            ‖F y - F xk - fderiv ℝ F xk (y - xk)‖ ≤ (1 - t) / Γ * ‖y - xk‖) →
          min (1 - ηbar) (θmin * δ / (Γ * ‖F xk‖)) ≤ 1 - trialLevel ηbar θ m := by
  have hnF : 0 < ‖F xk‖ := norm_pos_iff.mpr hFxk
  have hbar : ηbar ∈ Set.Icc ηbar 1 := ⟨le_rfl,hηbar.2.le⟩
  have hGp := NewtonLine.gamma_pos F xk ηbar hηbar.2 σ (hσ ηbar hbar) hFxk Γ (hΓ ηbar hbar)
  have hlev : ∀ n, ηbar ≤ trialLevel ηbar θ n ∧ trialLevel ηbar θ n < 1 :=
    fun n => NewtonTrials.levels ηbar θmin θmax hηbar hθ θ n (fun j _ => hθmem j)
  have hmem : ∀ n, trialLevel ηbar θ n ∈ Set.Icc ηbar 1 :=
    fun n => ⟨(hlev n).1,(hlev n).2.le⟩
  have hpass : ∃ n, SuffDecrease F t xk (σ (trialLevel ηbar θ n)) (trialLevel ηbar θ n) := by
    obtain ⟨δ,hδ,hr⟩ := NewtonLine.remainder F hF xk ((1-t)/Γ) (div_pos (sub_pos.mpr ht.2) hGp)
    have he := (NewtonTrials.gap_tendsto ηbar θmin θmax hηbar hθ θ hθmem).eventually
      (gt_mem_nhds (div_pos hδ (mul_pos hGp hnF)))
    obtain ⟨n,hn⟩ := he.exists
    refine ⟨n,NewtonLine.small_accept F xk t Γ (trialLevel ηbar θ n) δ ht.2 hGp
      (σ (trialLevel ηbar θ n)) (hσ _ (hmem n)) (hΓ _ (hmem n)) ?_ hr⟩
    have h := (lt_div_iff₀ (mul_pos hGp hnF)).mp hn
    nlinarith
  classical
  refine ⟨⟨Nat.find hpass,?_,Nat.find_spec hpass⟩,?_⟩
  · intro j hj
    exact Nat.find_min hpass hj
  · intro m hreject haccept δ hδ hrem
    cases m with
    | zero => simpa only [trialLevel] using min_le_left (1-ηbar) (θmin*δ/(Γ*‖F xk‖))
    | succ n =>
      have hbound : δ ≤ Γ*(1-trialLevel ηbar θ n)*‖F xk‖ := by
        by_contra! hsmall
        exact hreject n (Nat.lt_succ_self n)
          (NewtonLine.small_accept F xk t Γ (trialLevel ηbar θ n) δ ht.2 hGp
            (σ (trialLevel ηbar θ n)) (hσ _ (hmem n)) (hΓ _ (hmem n)) hsmall hrem)
      apply (min_le_right (1-ηbar) (θmin*δ/(Γ*‖F xk‖))).trans
      apply (div_le_iff₀ (mul_pos hGp hnF)).mpr
      have h1 := mul_le_mul_of_nonneg_left hbound hθ.1.le
      have hnon : 0 ≤ (1-trialLevel ηbar θ n)*Γ*‖F xk‖ :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr (hlev n).2.le) hGp.le) hnF.le
      have h2 := mul_le_mul_of_nonneg_right (hθmem n).1 hnon
      simp only [trialLevel]
      nlinarith

#print axioms solution
