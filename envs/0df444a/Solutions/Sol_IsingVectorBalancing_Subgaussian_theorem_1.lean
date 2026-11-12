-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:58.367343+00:00
-- url     : https://prove2.me/submissions/11bf2c7e-27cd-4507-bd3d-b4584769da61

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Law
import Theorems.Thm_IsingVectorBalancing_Subgaussian_theorem_9

section
set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian.Dev.T1
open IsingVectorBalancing.Subgaussian

def flip {n : ℕ} (σ : Configuration n) : Configuration n := fun i => !σ i

lemma flip_flip {n : ℕ} (σ : Configuration n) : flip (flip σ) = σ := by
  funext i; simp [flip]

lemma spin_not (b : Bool) : spin (!b) = - spin b := by
  cases b <;> simp [spin]

lemma weight_flip {n d : ℕ} (v : Fin n → Vec d) (σ : Configuration n) :
    weight v (flip σ) = weight v σ := by
  unfold weight
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp [flip, spin_not]

lemma probability_flip {n d : ℕ} (v : Fin n → Vec d) (σ : Configuration n) :
    probability v (fun _ => 0) (flip σ) = probability v (fun _ => 0) σ := by
  simp [probability, tiltedWeight, weight_flip]

lemma signedSum_flip {n d : ℕ} (v : Fin n → Vec d) (σ : Configuration n) :
    signedSum v (flip σ) = - signedSum v σ := by
  simp [signedSum, flip, spin_not, Finset.sum_neg_distrib]

lemma meanSum_zero {n d : ℕ} (v : Fin n → Vec d) : meanSum v (fun _ => 0) = 0 := by
  have e : Function.Involutive (flip (n := n)) := flip_flip
  have h1 : meanSum v (fun _ => 0) = - meanSum v (fun _ => 0) := by
    conv_lhs => rw [meanSum]
    rw [← Equiv.sum_comp e.toPerm]
    simp only [Function.Involutive.coe_toPerm, probability_flip, signedSum_flip, smul_neg,
      Finset.sum_neg_distrib]
    rfl
  set m := meanSum v (fun _ => 0) with hm
  have h2 : (2 : ℝ) • m = 0 := by
    rw [two_smul]; nth_rewrite 2 [h1]; exact add_neg_cancel m
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end IsingVectorBalancing.Subgaussian.Dev.T1

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.T1 in
theorem chk_theorem_1 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (θ : Vec d) :
    expectation v (fun _ => 0) (fun σ => Real.exp (inner ℝ θ (signedSum v σ))) ≤
      Real.exp (‖θ‖ ^ 2 / 2) := by
  have := theorem_9 v hv (fun _ => 0) θ
  simp only [meanSum_zero, sub_zero] at this
  exact this

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_theorem_1 := @IsingVectorBalancing.Subgaussian.chk_theorem_1
