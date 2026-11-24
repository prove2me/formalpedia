-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:28.151845+00:00
-- url     : https://prove2.me/submissions/68f30f4c-1fc6-483f-883c-44b49127da70

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_sum_Icc_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.TailIntegralOfSummatory
namespace GlobalTheory.TailIntegralOfSummatory
theorem _root_.solution (a : ℕ → ℂ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, psum a u / (u : ℂ) ^ 2 =
      (recSum a ⌊U⌋₊ - psum a U / U) - (recSum a ⌊y⌋₊ - psum a y / y) := by
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => ((t : ℂ))⁻¹) (-(((t : ℂ)) ^ 2)⁻¹) t := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    exact (hasDerivAt_inv ht').comp_ofReal
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => by
    have := ht.1
    intro h0
    linarith
  have hint : IntegrableOn (deriv (fun t : ℝ => ((t : ℂ))⁻¹)) (Set.Icc y U) := by
    have hc : ContinuousOn (fun t : ℝ => -(((t : ℂ)) ^ 2)⁻¹) (Set.Icc y U) := by
      refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro t ht
      exact pow_ne_zero _ (by exact_mod_cast hne t ht)
    refine (hc.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact ((hd t (hne t ht)).deriv).symm
  have key := sum_mul_eq_sub_sub_integral_mul (f := fun t : ℝ => ((t : ℂ))⁻¹)
    (fun k => if k = 0 then 0 else a k) (a := y) (b := U) (by linarith) hU
    (fun t ht => (hd t (hne t ht)).differentiableAt) hint
  simp only [sum_Icc_zero] at key
  have hfl : ⌊y⌋₊ ≤ ⌊U⌋₊ := Nat.floor_le_floor hU
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, (((k : ℝ) : ℂ))⁻¹ * (if k = 0 then 0 else a k)
      = recSum a ⌊U⌋₊ - recSum a ⌊y⌋₊ := by
    have e : ∀ N : ℕ, recSum a N = ∑ n ∈ Ioc 0 N, a n / (n : ℂ) := fun N => by
      unfold recSum
      rfl
    rw [e, e, eq_sub_iff_add_eq', ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    rw [if_neg this, div_eq_inv_mul]
    simp
  have hI : ∫ t in Set.Ioc y U, deriv (fun t : ℝ => ((t : ℂ))⁻¹) t * ∑ k ∈ Icc 1 ⌊t⌋₊, a k
      = -∫ u in y..U, psum a u / (u : ℂ) ^ 2 := by
    rw [intervalIntegral.integral_of_le hU, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have := (hd t (hne t ⟨ht.1.le, ht.2⟩)).deriv
    simp only [this, psum]
    ring
  rw [hL, hI] at key
  simp only [psum] at key ⊢
  linear_combination -key
end GlobalTheory.TailIntegralOfSummatory
