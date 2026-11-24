-- Prove2me | solution 1 for GlobalTheory.CuspGL.torus_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:35.525491+00:00
-- url     : https://prove2.me/submissions/d05d4ca5-a2e8-44b7-8e43-c8e005f310b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Theorems.Thm_GlobalTheory_CuspGL_minpoly_natDegree_dvd_iff_pow
import Theorems.Thm_GlobalTheory_CuspGL_roots_minpoly_eq_map_range
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
open Polynomial in
variable {F : Type} [Field F] [Finite F] in
private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e
end GlobalTheory.CuspGL
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
open Polynomial
variable {F : Type} [Field F] [Finite F]
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  intro F _ _ θ n hn α hα
  rw [Set.mem_setOf_eq] at hα
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold _root_.GlobalTheory.CuspGL.rootSum
  rw [Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
