-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T18:03:27.037244+00:00
-- url     : https://prove2.me/submissions/ef21e381-e6fe-4ccf-9072-b2a8c28f1f5c

import Init
import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

namespace NewtonInverse
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (hx : (fderiv ℝ F x).IsInvertible)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, (fderiv ℝ F y).IsInvertible ∧
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F x).inverse‖ < ε := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hc := (hF.continuous_fderiv one_ne_zero).continuousAt (x := x)
  have ho : ∀ᶠ y in 𝓝 x, (fderiv ℝ F y).IsInvertible :=
    hc.eventually (ContinuousLinearEquiv.isOpen.mem_nhds hx)
  have hi : ContinuousAt (fun y => (fderiv ℝ F y).inverse) x :=
    (hx.contDiffAt_map_inverse (n := 0)).continuousAt.comp hc
  have hn : ∀ᶠ y in 𝓝 x,
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F x).inverse‖ < ε := by
    simpa only [Metric.mem_ball,dist_eq_norm] using
      hi.eventually (Metric.ball_mem_nhds (fderiv ℝ F x).inverse hε)
  obtain ⟨δ,hδ,h⟩ := Metric.eventually_nhds_iff.mp (ho.and hn)
  exact ⟨δ,hδ,fun y hy => h (Metric.mem_ball.mp hy)⟩
#print axioms solution

end NewtonInverse

open Filter Topology
open GlobalInexactNewton.Backtracking
namespace NewtonBounds
lemma error_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (hx : (fderiv ℝ F x).IsInvertible) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ δ > 0, ∀ y ∈ Metric.ball x δ,
      ‖y-x‖ ≤ A*‖F y-F x‖ := by
  obtain ⟨e,he⟩ := hx
  have hd := hF.hasStrictFDerivAt (x := x) one_ne_zero
  rw [← he] at hd
  obtain ⟨s,hxs,hs,ha⟩ := hd.approximates_deriv_on_open_nhds
  have hanti := ha.antilipschitz
    (e.subsingleton_or_nnnorm_symm_pos.imp id fun h => NNReal.half_lt_self (ne_of_gt (inv_pos.mpr h)))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hxs)
  let K : NNReal := (‖(e.symm : E →L[ℝ] E)‖₊⁻¹ - ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ / 2)⁻¹
  refine ⟨(K:ℝ),K.coe_nonneg,δ,hδ,?_⟩
  intro y hy
  have h := hanti.le_mul_dist ⟨y,hball hy⟩ ⟨x,hxs⟩
  simpa only [Subtype.dist_eq,Set.restrict_apply,dist_eq_norm] using h
lemma local_step_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → E) (hF : ContDiff ℝ 1 F) (x : E)
    (hx : (fderiv ℝ F x).IsInvertible) (η : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ s,
      InexactNewtonCond F y s η → ‖s‖ ≤ B*‖F y‖ := by
  obtain ⟨δ,hδ,h⟩ := NewtonInverse.solution F hF x hx 1 zero_lt_one
  let K : ℝ := ‖(fderiv ℝ F x).inverse‖+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K*(|η|+1),mul_nonneg hK (by positivity),δ,hδ,?_⟩
  intro y hy s hs
  obtain ⟨hi,hn⟩ := h y hy
  have hnorm : ‖(fderiv ℝ F y).inverse‖ ≤ K := by
    have := norm_le_norm_sub_add (fderiv ℝ F y).inverse (fderiv ℝ F x).inverse
    dsimp [K]; linarith
  have heq : s = (fderiv ℝ F y).inverse (fderiv ℝ F y s) := (hi.inverse_apply_self s).symm
  have hder : ‖fderiv ℝ F y s‖ ≤ (|η|+1)*‖F y‖ := by
    have hb := norm_sub_le (F y + fderiv ℝ F y s) (F y)
    simp only [add_sub_cancel_left] at hb
    have he := mul_le_mul_of_nonneg_right (le_abs_self η) (norm_nonneg (F y))
    unfold InexactNewtonCond at hs
    nlinarith
  calc
    ‖s‖ = ‖(fderiv ℝ F y).inverse (fderiv ℝ F y s)‖ := congrArg norm heq
    _ ≤ ‖(fderiv ℝ F y).inverse‖*‖fderiv ℝ F y s‖ := (fderiv ℝ F y).inverse.le_opNorm _
    _ ≤ K*((|η|+1)*‖F y‖) := mul_le_mul hnorm hder (norm_nonneg _) hK
    _ = _ := by ring
end NewtonBounds
#print axioms NewtonBounds.error_bound
#print axioms NewtonBounds.local_step_bound

open Filter Topology
namespace NewtonTrap
lemma convergence {E : Type*} [NormedAddCommGroup E]
    (F : E → E) (x : ℕ → E) (xstar : E) (A B r : ℝ)
    (hr : 0 < r)
    (herror : ∀ y, ‖y-xstar‖ < r → ‖y-xstar‖ ≤ A*‖F y‖)
    (hstep : ∀ k, ‖x k-xstar‖ < r → ‖x (k+1)-x k‖ ≤ B*‖F (x k)‖)
    (hF0 : Tendsto (fun k => F (x k)) atTop (𝓝 0))
    (hlim : MapClusterPt xstar atTop x) : Tendsto x atTop (𝓝 xstar) := by
  have hnorm : Tendsto (fun k => ‖F (x k)‖) atTop (𝓝 0) := by simpa using hF0.norm
  have hA : Tendsto (fun k => A*‖F (x k)‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hnorm
  have hB : Tendsto (fun k => B*‖F (x k)‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hnorm
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmallA := hA.eventually (gt_mem_nhds (show 0 < min (r/2) ε from lt_min (by linarith) hε))
  have hsmallB := hB.eventually (gt_mem_nhds (show 0 < r/2 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsmallA.and hsmallB)
  have hf : ∃ᶠ k in atTop, ‖x k-xstar‖ < r/2 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using
      hlim.frequently (Metric.ball_mem_nhds xstar (show 0 < r/2 by linarith))
  obtain ⟨K,hK,hKN⟩ := (hf.and_eventually (eventually_ge_atTop N)).exists
  have hstay : ∀ k ≥ K, ‖x k-xstar‖ < r/2 := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base => exact hK
    | succ k hk ih =>
      have hn := hN k (hKN.trans hk)
      have hs := hstep k (by linarith)
      have hnext : ‖x (k+1)-xstar‖ < r := by
        have ht := norm_sub_le_norm_sub_add_norm_sub (x (k+1)) (x k) xstar
        linarith
      exact (herror _ hnext).trans_lt ((hN (k+1) (by omega)).1.trans_le (min_le_left _ _))
  refine ⟨K,?_⟩
  intro k hk
  rw [dist_eq_norm]
  exact (herror _ (by have := hstay k hk; linarith)).trans_lt
    ((hN k (hKN.trans hk)).1.trans_le (min_le_right _ _))
end NewtonTrap
#print axioms NewtonTrap.convergence

open Filter Topology
open GlobalInexactNewton.Backtracking

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : ℕ → E) (η : ℝ)
    (hF0 : Tendsto (fun k => F (x k)) atTop (𝓝 0))
    (hinexact : ∀ k, InexactNewtonCond F (x k) (x (k + 1) - x k) η)
    (hmono : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (xstar : E) (hlim : MapClusterPt xstar atTop x) (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) := by
  have hz : F xstar = 0 := by
    obtain ⟨φ,hφ,ht⟩ := hlim.tendsto_subseq
    exact tendsto_nhds_unique ((hF.continuous.tendsto xstar).comp ht) (hF0.comp hφ.tendsto_atTop)
  obtain ⟨A,hA,r,hr,he⟩ := NewtonBounds.error_bound F hF xstar hinv
  obtain ⟨B,hB,δ,hδ,hs⟩ := NewtonBounds.local_step_bound F hF xstar hinv η
  refine ⟨hz,NewtonTrap.convergence F x xstar A B (min r δ) (lt_min hr hδ) ?_ ?_ hF0 hlim⟩
  · intro y hy
    have h := he y (by rw [Metric.mem_ball,dist_eq_norm]; exact hy.trans_le (min_le_left _ _))
    simpa only [hz,sub_zero] using h
  · intro k hk
    exact hs (x k) (by rw [Metric.mem_ball,dist_eq_norm]; exact hk.trans_le (min_le_right _ _)) _ (hinexact k)
#print axioms solution
