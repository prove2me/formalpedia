-- Prove2me | solution 1 for MazurReduction.rational_torsion_kernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:35:58.659637+00:00
-- url     : https://prove2.me/submissions/e9882bb3-c521-4b9e-b787-681bb54014ef

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_MazurReduction_odd_prime_division_nonzero
import Theorems.Thm_MazurReduction_rational_residue_field_equiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine
open MazurReduction
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    [DecidableEq (ResidueField (Rat.padicValuation p).valuationSubring)]
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    [(W.map (Rat.padicValuation p).valuationSubring.subtype).IsElliptic]
    (hΔ : (W.map (residue (Rat.padicValuation p).valuationSubring)).Δ ≠ 0)
    (P : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Point)
    (hP : IsOfFinAddOrder P)
    (hred : WeierstrassCurve.reduceHom hΔ P = 0) : P = 0 := by
  classical
  let A := (Rat.padicValuation p).valuationSubring
  let F := ResidueField A
  obtain ⟨e⟩ := rational_residue_field_equiv p
  letI : CharP F p := charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  by_contra hP0
  have hn0 : addOrderOf P ≠ 0 := hP.addOrderOf_pos.ne'
  have hn1 : addOrderOf P ≠ 1 := fun h => hP0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
  let Q := (addOrderOf P / q) • P
  have hQorder : addOrderOf Q = q := by
    exact orderOf_pow_orderOf_div (x := Multiplicative.ofAdd P) hn0 hqdvd
  have hQred : WeierstrassCurve.reduceHom hΔ Q = 0 := by
    dsimp only [Q]
    rw [map_nsmul, hred, nsmul_zero]
  have hQq : q • Q = 0 := by rw [← hQorder]; exact addOrderOf_nsmul_eq_zero Q
  generalize hQdef : Q = R at hQorder hQred hQq
  cases R with
  | zero =>
    have hz : addOrderOf (0 : (W.map A.subtype).toAffine.Point) = q := hQorder
    exact hq.ne_one (by simpa only [addOrderOf_zero] using hz.symm)
  | some x y h =>
    have hx : x ∉ A := by
      intro hx
      have hs : WeierstrassCurve.reduceHom hΔ (.some x y h) ≠ 0 := by
        change WeierstrassCurve.reducePoint hΔ (.some x y h) ≠ 0
        rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx]
        exact Point.some_ne_zero _
      exact hs hQred
    by_cases hqp : q = p
    · rw [hqp] at hQq
      have hz := (Point.nsmul_some_eq_zero_iff_eval_prePsi
        (W.map A.subtype) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) h).mp hQq
      exact odd_prime_division_nonzero p hp W h.1 hx hz
    · have hqres : (q : F) ≠ 0 := by
        intro hz
        have hdiv := (CharP.cast_eq_zero_iff F p q).mp hz
        exact hqp ((Nat.dvd_prime hq).mp hdiv |>.resolve_left (Fact.out : p.Prime).ne_one).symm
      exact hx (WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hqres h hQq)
