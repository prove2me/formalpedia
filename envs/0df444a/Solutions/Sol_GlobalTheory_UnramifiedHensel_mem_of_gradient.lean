-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.mem_of_gradient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:17.097739+00:00
-- url     : https://prove2.me/submissions/01ba81ed-f3f2-45a8-a9b2-a588372c48c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
import Theorems.Thm_GlobalTheory_UnramifiedHensel_norm_sum_le_of_le
import Theorems.Thm_GlobalTheory_UnramifiedHensel_taylor_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]
namespace GlobalTheory.UnramifiedHensel
theorem _root_.solution [Fintype ι] [DecidableEq ι] (W : Subring K) (hW : IsClosed (W : Set K))
    (hc : ∀ w ∈ W, ‖w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (h0 : ∀ i, ∃ w ∈ W, ‖x i - w‖ < 1) (G : ι → MvPolynomial ι W)
    (hG : ∀ i, eval₂ W.subtype x (G i) = 0)
    (hd : ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ < 1) (i : ι) :
    x i ∈ W := by
  have hc' : ∀ w : W, ‖W.subtype w‖ ≤ 1 := fun w => hc w w.2
  choose y0 hy0W hy0 using h0
  obtain ⟨ρ, hρ0, hρ1, hρy, hρd⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (∀ i, ‖y0 i - x i‖ ≤ ρ) ∧
      ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ ≤ ρ := by
    refine ⟨max ‖fun i => y0 i - x i‖
      ‖fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖,
      le_max_of_le_left (norm_nonneg _), max_lt ?_ ?_, fun i => le_max_of_le_left ?_,
      fun i j => le_max_of_le_right ?_⟩
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [norm_sub_rev]; exact hy0 i
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [pi_norm_lt_iff one_pos]; exact hd i
    · exact norm_le_pi_norm (fun i => y0 i - x i) i
    · exact (norm_le_pi_norm
        (fun j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) j).trans
        (norm_le_pi_norm
        (fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) i)
  have key : ∀ n : ℕ, ∃ y : ι → W, ∀ i, ‖(y i : K) - x i‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨fun i => ⟨y0 i, hy0W i⟩, fun i => by simpa using hρy i⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨fun i => y i - eval y (G i), fun i => ?_⟩
      have hr : 0 ≤ ρ ^ (n + 1) := pow_nonneg hρ0 _
      have hT := taylor_bound W.subtype hc' x (fun i => (y i : K)) hx (fun i => hc' (y i)) hr hy
        (G i)
      have he : ((eval y (G i) : W) : K) = eval₂ W.subtype (fun i => (y i : K)) (G i) := by
        have := eval₂_comp_left W.subtype (RingHom.id W) y (G i)
        simpa [Function.comp_def] using this
      have : ((y i - eval y (G i) : W) : K) - x i =
          ∑ j, ((if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) * (y j - x j) +
          -(eval₂ W.subtype (fun i => (y i : K)) (G i) - eval₂ W.subtype x (G i) -
            ∑ j, eval₂ W.subtype x (pderiv j (G i)) * (y j - x j)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, hG, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        push_cast
        rw [he]; ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine norm_sum_le_of_le _ (pow_nonneg hρ0 _) fun j => ?_
        rw [norm_mul, pow_succ' ρ (n + 1)]
        exact mul_le_mul (hρd i j) (hy j) (norm_nonneg _) hρ0
      · rw [norm_neg, pow_succ ρ (n + 1)]
        refine hT.trans (mul_le_mul_of_nonneg_left ?_ hr)
        rw [pow_succ]
        exact mul_le_of_le_one_left hρ0 (pow_le_one₀ hρ0 hρ1.le)
  have : x i ∈ closure (W : Set K) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
    obtain ⟨y, hy⟩ := key n
    refine ⟨y i, (y i).2, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine (hy i).trans_lt (lt_of_le_of_lt ?_ hn)
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hρ0 _) hρ1.le
  rwa [hW.closure_eq] at this
end GlobalTheory.UnramifiedHensel
