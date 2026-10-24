-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.theorem_5_2_mr
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:20:38.021851+00:00
-- url     : https://prove2.me/submissions/283821e5-3759-4425-a5a8-c53295f313fd

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
namespace NewtonUniform
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem remainder (F : E → E) (hF : ContDiff ℝ 1 F) (xstar : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Metric.ball xstar δ, ∀ y ∈ Metric.ball xstar δ,
      ‖F y-F x-fderiv ℝ F x (y-x)‖ ≤ ε*‖y-x‖ := by
  have hc := (hF.continuous_fderiv one_ne_zero).continuousAt (x := xstar)
  obtain ⟨δ,hδ,hδmem⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (Metric.ball_mem_nhds (fderiv ℝ F xstar) (half_pos hε)))
  have hδbound : ∀ x ∈ Metric.ball xstar δ,
      ‖fderiv ℝ F x-fderiv ℝ F xstar‖ < ε/2 := by
    intro x hx
    simpa only [Metric.mem_ball,dist_eq_norm] using hδmem (Metric.mem_ball.mp hx)
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy
  have hd : ∀ z ∈ Metric.ball xstar δ,
      HasFDerivWithinAt (fun a => F a-fderiv ℝ F x a)
        (fderiv ℝ F z-fderiv ℝ F x) (Metric.ball xstar δ) z := by
    intro z hz
    exact ((hF.differentiable one_ne_zero z).hasFDerivAt.sub
      (fderiv ℝ F x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.ball xstar δ, ‖fderiv ℝ F z-fderiv ℝ F x‖ ≤ ε := by
    intro z hz
    have ht := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ F z) (fderiv ℝ F xstar) (fderiv ℝ F x)
    rw [norm_sub_rev (fderiv ℝ F xstar) (fderiv ℝ F x)] at ht
    linarith [hδbound x hx,hδbound z hz]
  have ht := (convex_ball xstar δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hx hy
  convert ht using 1 <;> congr 1 <;> simp only [map_sub] <;> abel

#print axioms remainder
end NewtonUniform

open Filter Topology GlobalInexactNewton.Backtracking
namespace NewtonExit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lower (F : E → E) (x : E) (t Γ B δ ηbar θmin θmax : ℝ)
    (ht : t < 1) (hΓ : 0 < Γ) (hB : 0 < B) (hδ : 0 < δ) (hFB : ‖F x‖ ≤ B)
    (hbar : ηbar ∈ Set.Ico (0:ℝ) 1) (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1)
    (σ : ℝ → E) (θ : ℕ → ℝ) (m : ℕ)
    (hmem : ∀ j < m, θ j ∈ Set.Icc θmin θmax)
    (hi : ∀ η ∈ Set.Icc ηbar 1, InexactNewtonCond F x (σ η) η)
    (hg : ∀ η ∈ Set.Icc ηbar 1, ‖σ η‖ ≤ Γ*(1-η)*‖F x‖)
    (hr : ∀ j < m, ¬ SuffDecrease F t x (σ (trialLevel ηbar θ j)) (trialLevel ηbar θ j))
    (hrem : ∀ y ∈ Metric.ball x δ,
      ‖F y-F x-fderiv ℝ F x (y-x)‖ ≤ (1-t)/Γ*‖y-x‖) :
    min (1-ηbar) (θmin*δ/(Γ*B)) ≤ 1-trialLevel ηbar θ m := by
  cases m with
  | zero => simpa only [trialLevel] using min_le_left (1-ηbar) (θmin*δ/(Γ*B))
  | succ n =>
    have hl := NewtonTrials.levels ηbar θmin θmax hbar hθ θ n
      (fun j hj => hmem j (Nat.lt_succ_of_lt hj))
    have hb : δ ≤ Γ*(1-trialLevel ηbar θ n)*‖F x‖ := by
      by_contra! hsmall
      exact hr n (Nat.lt_succ_self n)
        (NewtonLine.small_accept F x t Γ (trialLevel ηbar θ n) δ ht hΓ
          (σ (trialLevel ηbar θ n)) (hi _ ⟨hl.1,hl.2.le⟩) (hg _ ⟨hl.1,hl.2.le⟩) hsmall hrem)
    have hupper := mul_le_mul_of_nonneg_left hFB (mul_nonneg hΓ.le (sub_nonneg.mpr hl.2.le))
    have h1 := mul_le_mul_of_nonneg_left (hb.trans hupper) hθ.1.le
    have h2 := mul_le_mul_of_nonneg_right (hmem n (Nat.lt_succ_self n)).1
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hl.2.le) hΓ.le) hB.le)
    apply (min_le_right (1-ηbar) (θmin*δ/(Γ*B))).trans
    apply (div_le_iff₀ (mul_pos hΓ hB)).mpr
    simp only [trialLevel]
    nlinarith

#print axioms lower
end NewtonExit

open Filter Topology
open GlobalInexactNewton.Backtracking

theorem mr_is_gin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ) (σ : ℕ → ℝ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m) :
    IsGINRun F t x (fun k => trialLevel (ηbar k) (θ k) (m k)) := by
  have hl : ∀ k, ηbar k ≤ trialLevel (ηbar k) (θ k) (m k) ∧
      trialLevel (ηbar k) (θ k) (m k) < 1 := by
    intro k
    exact NewtonTrials.levels (ηbar k) θmin θmax
      ⟨(hrun.ηbar_mem k).1,lt_of_le_of_lt (hrun.ηbar_mem k).2 hrun.ηmax_mem.2⟩
      hrun.θ_bounds (θ k) (m k) (hrun.θ_mem k)
  refine ⟨hrun.t_mem,?_,?_,?_⟩
  · intro k
    exact ⟨(hrun.ηbar_mem k).1.trans (hl k).1,(hl k).2⟩
  · intro k
    rw [hrun.step k,add_sub_cancel_left]
    exact hrun.curve k _ ⟨(hl k).1,(hl k).2.le⟩
  · intro k
    rw [hrun.step k,add_sub_cancel_left]
    exact hrun.accepted k

#print axioms mr_is_gin

open Filter Topology
namespace NewtonVariation
lemma convergence {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (xstar : E) (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hm : Antitone ρ)
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (K₀ : ℕ)
    (hstep : ∀ k ≥ K₀, ‖x k-xstar‖ < δ →
      ‖x (k+1)-x k‖ ≤ C*(ρ k-ρ (k+1)))
    (hlim : MapClusterPt xstar atTop x) : Tendsto x atTop (𝓝 xstar) := by
  let L := ⨅ n,ρ n
  have hb : BddBelow (Set.range ρ) := ⟨0,Set.forall_mem_range.mpr hρ⟩
  have hL : ∀ n, L ≤ ρ n := fun n => ciInf_le hb n
  have ht : Tendsto ρ atTop (𝓝 L) := tendsto_atTop_ciInf hm hb
  have htC : Tendsto (fun n => C*(ρ n-L)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul (ht.sub (tendsto_const_nhds (x := L)))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let e := min δ ε / 3
  have he : 0 < e := div_pos (lt_min hδ hε) (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (htC.eventually (gt_mem_nhds he))
  have hf : ∃ᶠ k in atTop, ‖x k-xstar‖ < e := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hlim.frequently (Metric.ball_mem_nhds xstar he)
  obtain ⟨K,hK,hKN⟩ := (hf.and_eventually (eventually_ge_atTop (max N K₀))).exists
  have hKN' : N ≤ K := (le_max_left _ _).trans hKN
  have hKK : K₀ ≤ K := (le_max_right _ _).trans hKN
  have htail : ∀ k, C*(ρ K-ρ k) < e := by
    intro k
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hL k) _) hC).trans_lt (hN K hKN')
  have hp : ∀ k ≥ K, ‖x k-x K‖ ≤ C*(ρ K-ρ k) := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hnear : ‖x k-xstar‖ < δ := by
        have htri := norm_sub_le_norm_sub_add_norm_sub (x k) (x K) xstar
        have hbnd := htail k
        have hmin := min_le_left δ ε
        dsimp [e] at *
        linarith
      have hs := hstep k (hKK.trans hk) hnear
      have htri := norm_sub_le_norm_sub_add_norm_sub (x (k+1)) (x k) (x K)
      nlinarith
  refine ⟨K,?_⟩
  intro k hk
  rw [dist_eq_norm]
  have htri := norm_sub_le_norm_sub_add_norm_sub (x k) (x K) xstar
  have hpath := hp k hk
  have hbnd := htail k
  have hmin := min_le_right δ ε
  dsimp [e] at *
  linarith
end NewtonVariation
#print axioms NewtonVariation.convergence

open Filter Topology
open GlobalInexactNewton.Backtracking

theorem prior_steps_converge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t : ℝ) (x : ℕ → E) (η : ℕ → ℝ)
    (hrun : IsGINRun F t x η) (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ δ > 0, ∃ K : ℕ, ∀ k ≥ K, x k ∈ Metric.ball xstar δ →
      ‖x (k + 1) - x k‖ ≤ Γ * (1 - η k) * ‖F (x k)‖) :
    Tendsto x atTop (𝓝 xstar) := by
  obtain ⟨Γ,δ,hδ,K,hstep⟩ := hΓ
  have ht : 0 < t := hrun.t_mem.1
  have ha : ∀ k, 0 ≤ 1-η k := fun k => sub_nonneg.mpr (hrun.eta_mem k).2.le
  have hd : ∀ k, ‖F (x (k+1))‖ ≤ (1-t*(1-η k))*‖F (x k)‖ := by
    intro k
    simpa [SuffDecrease] using hrun.decrease k
  have hm : Antitone (fun k => ‖F (x k)‖) := antitone_nat_of_succ_le (fun k => by
    have hp := mul_nonneg (mul_nonneg ht.le (ha k)) (norm_nonneg (F (x k)))
    have h := hd k
    nlinarith)
  let C : ℝ := |Γ|/t
  have hC : 0 ≤ C := div_nonneg (abs_nonneg _) ht.le
  apply NewtonVariation.convergence x xstar (fun k => ‖F (x k)‖) (fun k => norm_nonneg _) hm C δ hC hδ K ?_ hlim
  intro k hk hnear
  calc
    ‖x (k+1)-x k‖ ≤ Γ*(1-η k)*‖F (x k)‖ := hstep k hk (by simpa only [Metric.mem_ball,dist_eq_norm] using hnear)
    _ ≤ |Γ| *(1-η k)*‖F (x k)‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Γ) (ha k)) (norm_nonneg _)
    _ = C*(t*(1-η k)*‖F (x k)‖) := by dsimp [C]; field_simp [ne_of_gt ht]
    _ ≤ C*(‖F (x k)‖-‖F (x (k+1))‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have h := hd k
      nlinarith
#print axioms prior_steps_converge

open Filter Topology GlobalInexactNewton.Backtracking

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m)
    (xstar : E) (hlim : MapClusterPt xstar atTop x)
    (hΓ : ∃ Γ : ℝ, ∃ δ > 0, ∀ k, x k ∈ Metric.ball xstar δ →
      ∀ η ∈ Set.Icc (ηbar k) 1, ‖σ k η‖ ≤ Γ * (1 - η) * ‖F (x k)‖) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by
  obtain ⟨Γ,r,hr,hbound⟩ := hΓ
  let G := |Γ|+1
  have hG : 0 < G := by dsimp [G]; positivity
  have hGΓ : Γ ≤ G := by dsimp [G]; linarith [le_abs_self Γ]
  have hg : ∀ k, x k ∈ Metric.ball xstar r → ∀ η ∈ Set.Icc (ηbar k) 1,
      ‖σ k η‖ ≤ G*(1-η)*‖F (x k)‖ := by
    intro k hk η hη
    exact (hbound k hk η hη).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hGΓ (sub_nonneg.mpr hη.2)) (norm_nonneg _))
  have hb : ∀ k, ηbar k ∈ Set.Ico (0:ℝ) 1 := fun k =>
    ⟨(hrun.ηbar_mem k).1,(hrun.ηbar_mem k).2.trans_lt hrun.ηmax_mem.2⟩
  have hl : ∀ k, ηbar k ≤ trialLevel (ηbar k) (θ k) (m k) ∧ trialLevel (ηbar k) (θ k) (m k) < 1 :=
    fun k => NewtonTrials.levels (ηbar k) θmin θmax (hb k) hrun.θ_bounds (θ k) (m k) (hrun.θ_mem k)
  have hgin := mr_is_gin F ηmax t θmin θmax x ηbar σ θ m hrun
  have hconv : Tendsto x atTop (𝓝 xstar) := by
    apply prior_steps_converge F hF t x (fun k => trialLevel (ηbar k) (θ k) (m k)) hgin xstar hlim
    refine ⟨G,r,hr,0,?_⟩
    intro k hk hx
    rw [hrun.step k,add_sub_cancel_left]
    exact hg k hx _ ⟨(hl k).1,(hl k).2.le⟩
  obtain ⟨ρ,hρ,hrem⟩ := NewtonUniform.remainder F hF xstar ((1-t)/G)
    (div_pos (sub_pos.mpr hrun.t_mem.2) hG)
  let δ := min r (ρ/2)
  have hδ : 0 < δ := lt_min hr (half_pos hρ)
  have hlocal : ∀ k, x k ∈ Metric.ball xstar δ →
      (∀ η ∈ Set.Icc (ηbar k) 1, ‖σ k η‖ ≤ G*(1-η)*‖F (x k)‖) ∧
      (∀ y ∈ Metric.ball (x k) δ,
        ‖F y-F (x k)-fderiv ℝ F (x k) (y-x k)‖ ≤ (1-t)/G*‖y-x k‖) := by
    intro k hk
    have hkr : x k ∈ Metric.ball xstar r := Metric.ball_subset_ball (min_le_left _ _) hk
    have hkρ : x k ∈ Metric.ball xstar ρ := Metric.ball_subset_ball
      ((min_le_right _ _).trans (half_le_self hρ.le)) hk
    refine ⟨hg k hkr,?_⟩
    intro y hy
    apply hrem (x k) hkρ y
    rw [Metric.mem_ball] at hk hy ⊢
    have htri := dist_triangle y (x k) xstar
    have hdρ := min_le_right r (ρ/2)
    dsimp [δ] at hk hy
    linarith
  have hnear : ∀ᶠ k in atTop, x k ∈ Metric.ball xstar δ :=
    hconv.eventually (Metric.ball_mem_nhds xstar hδ)
  have hnorm : Tendsto (fun k => ‖F (x k)‖) atTop (𝓝 ‖F xstar‖) :=
    (hF.continuous.continuousAt.tendsto.comp hconv).norm
  let B := ‖F xstar‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbounded : ∀ᶠ k in atTop, ‖F (x k)‖ < B :=
    hnorm.eventually (gt_mem_nhds (by dsimp [B]; linarith))
  let c := min (1-ηmax) (θmin*δ/(G*B))
  have hc : 0 < c := lt_min (sub_pos.mpr hrun.ηmax_mem.2)
    (div_pos (mul_pos hrun.θ_bounds.1 hδ) (mul_pos hG hB))
  have hgap : ∀ᶠ k in atTop, c ≤ 1-trialLevel (ηbar k) (θ k) (m k) := by
    filter_upwards [hnear,hbounded] with k hk hBk
    have h := NewtonExit.lower F (x k) t G B δ (ηbar k) θmin θmax hrun.t_mem.2 hG hB hδ hBk.le
      (hb k) hrun.θ_bounds (σ k) (θ k) (m k) (hrun.θ_mem k) (hrun.curve k)
      (hlocal k hk).1 (hrun.rejected k) (hlocal k hk).2
    exact (min_le_min (sub_le_sub_left (hrun.ηbar_mem k).2 1) le_rfl).trans h
  have hdecrease : ∀ᶠ k in atTop, ‖F (x (k+1))‖ ≤ (1-t*c)*‖F (x k)‖ := by
    filter_upwards [hgap] with k hk
    have hd := hgin.decrease k
    simp only [SuffDecrease,add_sub_cancel] at hd
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hrun.t_mem.1.le)
      (norm_nonneg (F (x k)))
    nlinarith
  have hshift : Tendsto (fun k => ‖F (x (k+1))‖) atTop (𝓝 ‖F xstar‖) :=
    hnorm.comp (tendsto_add_atTop_nat 1)
  have hlimit := le_of_tendsto_of_tendsto hshift (hnorm.const_mul (1-t*c)) hdecrease
  have hzero : F xstar = 0 := by
    by_contra hn
    have hp := mul_pos (mul_pos hrun.t_mem.1 hc) (norm_pos_iff.mpr hn)
    nlinarith
  refine ⟨hzero,hconv,?_⟩
  have hsmall : ∀ᶠ k in atTop, G*‖F (x k)‖ < δ := by
    have htend := hnorm.const_mul G
    rw [hzero,norm_zero,mul_zero] at htend
    exact htend.eventually (gt_mem_nhds hδ)
  filter_upwards [hnear,hsmall] with k hk hsk
  have htest : SuffDecrease F t (x k) (σ k (ηbar k)) (ηbar k) := by
    apply NewtonLine.small_accept F (x k) t G (ηbar k) δ hrun.t_mem.2 hG (σ k (ηbar k))
      (hrun.curve k _ ⟨le_rfl,(hb k).2.le⟩) ((hlocal k hk).1 _ ⟨le_rfl,(hb k).2.le⟩)
      ?_ (hlocal k hk).2
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show 1-ηbar k ≤ 1 by linarith [(hb k).1]) hG.le)
      (norm_nonneg (F (x k)))
    nlinarith
  have hmzero : m k = 0 := by
    by_contra hm
    exact (hrun.rejected k 0 (Nat.pos_of_ne_zero hm)) (by simpa only [trialLevel] using htest)
  simp only [hmzero,trialLevel]

#print axioms solution
