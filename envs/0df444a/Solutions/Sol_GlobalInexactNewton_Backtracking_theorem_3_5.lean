-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T18:09:52.801667+00:00
-- url     : https://prove2.me/submissions/2b391b59-b078-47b7-8e27-72eb0d4b2ee9

import Init
import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
#print axioms solution
