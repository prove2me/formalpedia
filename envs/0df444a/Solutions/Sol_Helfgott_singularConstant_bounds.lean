-- Prove2me | solution 1 for Helfgott.singularConstant_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T02:43:47.538061+00:00
-- url     : https://prove2.me/submissions/fde32810-df4f-4f70-b9e4-ef2fc80d0849

import Definitions.Def_Helfgott_SingularSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Uniform upper bound for the actual ternary Euler constant. Complete convergence and factor proofs included. Written by Codex. -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott

lemma singularEulerFactor_norm_defect_bound (N p : ℕ) :
    ‖singularEulerFactor N p-1‖ ≤ 4/(p:ℝ)^2 := by
  unfold singularEulerFactor
  split_ifs with hp hdvd
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hsq : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
    have hp2 : (0:ℝ) < (p:ℝ)^2 := by positivity
    have hcomp : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      apply (div_le_div_iff₀ hsq hp2).2
      nlinarith [sq_nonneg ((p:ℝ)-2)]
    have hid : (1-1/((p:ℝ)-1)^2)-1 = -(1/((p:ℝ)-1)^2) := by ring
    rw [hid,norm_neg,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hcomp
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have ha : (1:ℝ) ≤ (p:ℝ)-1 := by linarith
    have hsq : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
    have hp2 : (0:ℝ) < (p:ℝ)^2 := by positivity
    have hcomp : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      apply (div_le_div_iff₀ hsq hp2).2
      nlinarith [sq_nonneg ((p:ℝ)-2)]
    have hden : ((p:ℝ)-1)^2 ≤ ((p:ℝ)-1)^3 := by
      nlinarith [mul_nonneg (sq_nonneg ((p:ℝ)-1)) (sub_nonneg.mpr ha)]
    have hc : 1/((p:ℝ)-1)^3 ≤ 1/((p:ℝ)-1)^2 :=
      one_div_le_one_div_of_le hsq hden
    have hid : (1+1/((p:ℝ)-1)^3)-1 = 1/((p:ℝ)-1)^3 := by ring
    have hcube : 0 ≤ 1/((p:ℝ)-1)^3 := by positivity
    rw [hid,Real.norm_eq_abs,abs_of_nonneg hcube]
    exact hc.trans hcomp
  · simp only [sub_self,norm_zero]
    positivity

lemma singularEulerFactor_summable_defect (N : ℕ) :
    Summable (fun p : ℕ => ‖singularEulerFactor N p-1‖) := by
  have hs : Summable (fun p : ℕ => 4/(p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))).mul_left (4:ℝ))
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => singularEulerFactor_norm_defect_bound N p)

lemma singularEulerFactor_multipliable (N : ℕ) : Multipliable (singularEulerFactor N) := by
  have hm := multipliable_one_add_of_summable (singularEulerFactor_summable_defect N)
  have he : (fun p : ℕ => 1+(singularEulerFactor N p-1)) = singularEulerFactor N := by
    funext p
    ring
  rw [he] at hm
  exact hm

lemma singularEulerFactor_nonneg (N p : ℕ) : 0 ≤ singularEulerFactor N p := by
  unfold singularEulerFactor
  split_ifs with hp hdvd
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hs : (1:ℝ) ≤ ((p:ℝ)-1)^2 := by nlinarith
    have hpos : (0:ℝ) < ((p:ℝ)-1)^2 := by linarith
    have hi : 1/((p:ℝ)-1)^2 ≤ (1:ℝ) := (div_le_one hpos).2 hs
    linarith
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hden0 : (0:ℝ) ≤ (p:ℝ)-1 := by linarith
    have hc : (0:ℝ) ≤ 1/((p:ℝ)-1)^3 := by positivity
    linarith
  · norm_num


end Helfgott
end

section
open Finset
open scoped BigOperators
namespace Helfgott.SingularAux
lemma prod_one_add_times_one_sub_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hf a (mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hi := ih hs0
    have hP : 0 ≤ ∏ i ∈ s, (1+f i) := prod_nonneg (fun i hi => by linarith [hs0 i hi])
    have hS : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hs0
    rw [prod_insert ha,sum_insert ha]
    have hh : (1+f a)*(1-(f a+∑ i ∈ s,f i)) ≤ 1-∑ i ∈ s,f i := by
      nlinarith [mul_nonneg ha0 hS, sq_nonneg (f a)]
    calc
      _ = (∏ i ∈ s, (1+f i))*((1+f a)*(1-(f a+∑ i ∈ s,f i))) := by ring
      _ ≤ (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s,f i) := mul_le_mul_of_nonneg_left hh hP
      _ ≤ 1 := hi


end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Finset
open scoped BigOperators

namespace Helfgott
namespace SingularUpperAux

lemma inv_cube_telescoping (t : ℝ) (ht : 2 ≤ t) :
    1/(t+1)^3 ≤ (1/2:ℝ)*(1/t^2-1/(t+1)^2) := by
  have ht0 : 0 < t := by linarith
  have htp : 0 < t+1 := by linarith
  apply (div_le_iff₀ (pow_pos htp 3)).mpr
  field_simp
  nlinarith

lemma inv_cube_tail_finite (M : ℕ) :
    ∑ k ∈ range M, 1/((k:ℝ)+3)^3 ≤ (1/8:ℝ)-(1/2:ℝ)/((M:ℝ)+2)^2 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [sum_range_succ]
    have h := inv_cube_telescoping ((M:ℝ)+2) (by linarith [Nat.cast_nonneg (α:=ℝ) M])
    rw [show (M:ℝ)+2+1 = (M:ℝ)+3 by ring] at h
    simp only [Nat.cast_succ]
    rw [show (M:ℝ)+1+2 = (M:ℝ)+3 by ring]
    calc
      _ ≤ ((1/8:ℝ)-(1/2:ℝ)/((M:ℝ)+2)^2) +
          (1/2:ℝ)*(1/((M:ℝ)+2)^2-1/((M:ℝ)+3)^2) := add_le_add ih h
      _ = _ := by ring

lemma inv_cube_prefix (M : ℕ) :
    ∑ k ∈ range M, 1/((k:ℝ)+2)^3 ≤ (1/4:ℝ) := by
  cases M with
  | zero => norm_num
  | succ M =>
    rw [sum_range_succ']
    simp only [Nat.cast_succ,Nat.cast_zero,zero_add]
    have h := inv_cube_tail_finite M
    have he : (fun k : ℕ => 1/((k:ℝ)+1+2)^3) =
        (fun k : ℕ => 1/((k:ℝ)+3)^3) := by funext k;congr 2;ring
    rw [he]
    rw [show (1/(2:ℝ)^3:ℝ) = 1/8 by norm_num]
    have hn : 0 ≤ (1/2:ℝ)/((M:ℝ)+2)^2 := by positivity
    linarith

lemma inv_cube_product (M : ℕ) :
    ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) ≤ (4/3:ℝ) := by
  have hh := SingularAux.prod_one_add_times_one_sub_sum_le (range M)
    (fun k : ℕ => 1/((k:ℝ)+2)^3) (fun k _ => by positivity)
  have hs := inv_cube_prefix M
  have hp : 0 ≤ ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) :=
    prod_nonneg (fun k _ => by positivity)
  nlinarith

lemma singular_factor_upper (N k : ℕ) :
    singularEulerFactor N (k+3) ≤ 1+1/((k:ℝ)+2)^3 := by
  have he : ((k+3:ℕ):ℝ)-1 = (k:ℝ)+2 := by push_cast;ring
  by_cases hp : Nat.Prime (k+3)
  · by_cases hd : k+3 ∣ N
    · simp only [singularEulerFactor,if_pos hp,if_pos hd,he]
      have h2 : 0 ≤ 1/((k:ℝ)+2)^2 := by positivity
      have h3 : 0 ≤ 1/((k:ℝ)+2)^3 := by positivity
      linarith
    · simp only [singularEulerFactor,if_pos hp,if_neg hd,he]
      exact le_rfl
  · simp only [singularEulerFactor,if_neg hp]
    linarith [show (0:ℝ) ≤ 1/((k:ℝ)+2)^3 by positivity]

lemma singular_prefix_three (N : ℕ) :
    ∏ p ∈ range 3, singularEulerFactor N p ≤ 2 := by
  norm_num [prod_range_succ,singularEulerFactor]
  split_ifs <;> norm_num

lemma singular_partial_upper (N Q : ℕ) :
    ∏ p ∈ range Q, singularEulerFactor N p ≤ (8/3:ℝ) := by
  by_cases hQ : Q < 3
  · interval_cases Q <;> norm_num [prod_range_succ,singularEulerFactor]
  · obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ Q)
    rw [prod_range_add]
    have hp : 0 ≤ ∏ k ∈ range M, singularEulerFactor N (3+k) :=
      prod_nonneg (fun k _ => singularEulerFactor_nonneg N (3+k))
    have hc : (∏ k ∈ range M, singularEulerFactor N (3+k)) ≤
        ∏ k ∈ range M, (1+1/((k:ℝ)+2)^3) := by
      apply Finset.prod_le_prod
      · exact fun k _ => singularEulerFactor_nonneg N (3+k)
      · intro k hk
        simpa only [Nat.add_comm] using singular_factor_upper N k
    have ht := hc.trans (inv_cube_product M)
    have hh := mul_le_mul (singular_prefix_three N) ht hp (by norm_num : (0:ℝ) ≤ 2)
    nlinarith

end SingularUpperAux

theorem singularConstant_upper (N : ℕ) : singularConstant N ≤ (8/3:ℝ) := by
  apply le_of_tendsto (singularEulerFactor_multipliable N).tendsto_prod_tprod_nat
  exact Filter.Eventually.of_forall (SingularUpperAux.singular_partial_upper N)

theorem singularConstant_bounds (N : ℕ) :
    0 ≤ singularConstant N ∧ singularConstant N ≤ (8/3:ℝ) := by
  exact ⟨tprod_nonneg (fun p => singularEulerFactor_nonneg N p),singularConstant_upper N⟩

end Helfgott
end

theorem solution (N : ℕ) :
    0 ≤ Helfgott.singularConstant N ∧ Helfgott.singularConstant N ≤ (8/3:ℝ) :=
  Helfgott.singularConstant_bounds N

#print axioms solution
