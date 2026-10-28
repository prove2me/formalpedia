-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:25:31.480208+00:00
-- url     : https://prove2.me/submissions/76526eaf-b6b7-4c31-918a-20ba0cba68f7

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (e : Fin (m + 1) → Nat) :
    ∀ j k : Fin K, j ≠ k →
      IsCoprime
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e)
        (logarithmicCenterIdeal (c k) (fun _ => e 0) e) := by
  intro j k hjk
  let i0 : Fin m := ⟨0, hm⟩
  have hne : c j i0 ≠ c k i0 := fun h => hjk (hc i0 h)
  set L : MvPolynomial (Fin (m + 1)) ℂ :=
    Polynomial.aeval (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) ℂ)
      (InterpolationMatrix.truncatedLog (e 0)) with hL
  have hj : logarithmicCoordinate (c j) (fun _ => e 0) i0.succ =
      MvPolynomial.X i0.succ - MvPolynomial.C (c j i0) - L := rfl
  have hk : logarithmicCoordinate (c k) (fun _ => e 0) i0.succ =
      MvPolynomial.X i0.succ - MvPolynomial.C (c k i0) - L := rfl
  have hcop : IsCoprime (logarithmicCoordinate (c j) (fun _ => e 0) i0.succ)
      (logarithmicCoordinate (c k) (fun _ => e 0) i0.succ) := by
    rw [hj, hk]
    have hd : (c k i0 - c j i0) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    refine ⟨MvPolynomial.C (c k i0 - c j i0)⁻¹, -MvPolynomial.C (c k i0 - c j i0)⁻¹, ?_⟩
    have : MvPolynomial.C (c k i0 - c j i0)⁻¹ * MvPolynomial.C (c k i0 - c j i0) =
        (1 : MvPolynomial (Fin (m + 1)) ℂ) := by
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]
    rw [← this, map_sub]; ring
  have hcop2 := hcop.pow (m := e i0.succ) (n := e i0.succ)
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq] at hcop2
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hcop2]
  apply sup_le_sup
  · rw [Ideal.span_le]; rintro _ rfl
    exact Ideal.subset_span ⟨i0.succ, rfl⟩
  · rw [Ideal.span_le]; rintro _ rfl
    exact Ideal.subset_span ⟨i0.succ, rfl⟩
