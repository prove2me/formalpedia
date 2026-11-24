-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:49:00.988986+00:00
-- url     : https://prove2.me/submissions/b0dd471e-da7f-4d7f-aacb-50e0f0d02b58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
import Theorems.Thm_GlobalTheory_PrimeMeanValue_conj_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) * ‖a n‖ ^ 2 := by
  have e1 : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m *
        (if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0) := by
    push_cast
    have : ∀ χ : DirichletCharacter ℂ q, ((‖∑ n ∈ S, a n * χ (n : ZMod q)‖ : ℝ) : ℂ) ^ 2 =
        ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m * (χ (n : ZMod q)⁻¹ * χ (m : ZMod q)) := by
      intro χ
      rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, conj_char χ ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
  set g : ℕ → ℕ → ℝ := fun n m => if (n : ZMod q) = (m : ZMod q) then (q.totient : ℝ) else 0
    with hg
  have hsym : ∀ n m, g n m = g m n := fun n m => by simp only [hg, eq_comm]
  have hg0 : ∀ n m, 0 ≤ g n m := fun n m => by simp only [hg]; split_ifs <;> positivity
  have e2 : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖a n‖ ^ 2 * g n m / 2 + ‖a m‖ ^ 2 * g n m / 2) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, e1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have : ‖(if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0)‖ = g n m := by
      simp only [hg]; split_ifs <;> simp
    rw [norm_mul, norm_mul, this, Complex.norm_conj]
    have := hg0 n m
    nlinarith [mul_nonneg this (sq_nonneg (‖a n‖ - ‖a m‖))]
  refine e2.trans (le_of_eq ?_)
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun n m => ‖a m‖ ^ 2 * g n m / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hsym n m]
  simp only [hg, ZMod.natCast_eq_natCast_iff]
  split_ifs <;> ring
end GlobalTheory.PrimeMeanValue
