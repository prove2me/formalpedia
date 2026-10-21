-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_quotient_representatives_imply_strict_power_generators
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:43:43.944986+00:00
-- url     : https://prove2.me/submissions/57f3ad77-cb04-45d4-bc7d-ec16f73c0395

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_span_of_bounded_weight_representatives

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat) (R : Rat)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hR : 0 < R) (hw : ∀ i, 0 < (w i : Real))
    (δ : Rat) (hδpos : 0 < δ) (hδR : δ < R)
    (n₀ : Nat)
    (hrep : ∀ n : Nat, n₀ ≤ n → ∀ p : MvPolynomial (Fin (m + 1)) Complex,
      ∃ q : MvPolynomial (Fin (m + 1)) Complex,
        p - q ∈ I ^ n ∧
        ∀ a ∈ q.support,
          ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * (δ : Real)) :
    ∃ s : Nat, ∃ D : Rat,
      (D : Real) < (s : Real) * (R : Real) ∧
      I ^ s = Ideal.span {p : MvPolynomial (Fin (m + 1)) Complex |
        p ∈ I ^ s ∧
        ∀ a ∈ p.support, ∑ i, (w i : Real) * (a i : Real) ≤ (D : Real)} := by
  classical
  let W : Rat := ∑ i, w i
  have hgap : (0 : Rat) < R - δ := sub_pos.mpr hδR
  obtain ⟨s, hs⟩ := exists_nat_gt (max (n₀ : Rat) (W / (R - δ)))
  have hthreshold : (n₀ : Rat) < (s : Rat) :=
    lt_of_le_of_lt (le_max_left _ _) hs
  have hns : n₀ ≤ s := by
    exact_mod_cast hthreshold.le
  have hratio : W / (R - δ) < (s : Rat) :=
    lt_of_le_of_lt (le_max_right _ _) hs
  have hlarge : W < (s : Rat) * (R - δ) :=
    (div_lt_iff₀ hgap).mp hratio
  have hstrict : (s : Rat) * δ + W < (s : Rat) * R := by
    nlinarith only [hlarge]
  have hδreal : (0 : Real) < (δ : Real) := by
    exact_mod_cast hδpos
  have hnonneg : (0 : Real) ≤ (s : Real) * (δ : Real) :=
    mul_nonneg (Nat.cast_nonneg s) hδreal.le
  have hspan :=
    OAI.PiExponent.FormalInterpolation.ideal_span_of_bounded_weight_representatives
      m (fun i => (w i : Real)) hw (I ^ s)
      ((s : Real) * (δ : Real)) hnonneg (hrep s hns)
  refine ⟨s, (s : Rat) * δ + W, ?_, ?_⟩
  · exact_mod_cast hstrict
  · simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, W, Rat.cast_sum]
      using hspan.symm