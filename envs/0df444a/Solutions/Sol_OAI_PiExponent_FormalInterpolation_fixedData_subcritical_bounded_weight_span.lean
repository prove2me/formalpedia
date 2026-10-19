-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_subcritical_bounded_weight_span
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:27:04.823425+00:00
-- url     : https://prove2.me/submissions/aeb28f0d-33ec-457f-a57b-85dc7c6e0b3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_canonical_power_le
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_strict_power_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_span_of_bounded_weight_representatives
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation


theorem row_scale_truncation_cutoff {m : Nat}
    (v0 theta R : Real) (w : Fin m → Real)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (hv0 : 0 < v0)
    (hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0)
    (hscale : ∀ i, R = (e i : Real) *
      InterpolationMatrix.rowWeights v0 theta w i) :
    ∀ i, e 0 ≤ T i * e i.succ := by
  intro i
  have hzero : R = (e 0 : Real) * v0 := by
    simpa only [InterpolationMatrix.rowWeights, Fin.cases_zero] using hscale 0
  have hsucc : R = (e i.succ : Real) * (w i / theta) := by
    simpa only [InterpolationMatrix.rowWeights, Fin.cases_succ] using hscale i.succ
  have htrunc : w i / theta ≤ (T i : Real) * v0 := by
    simpa only [InterpolationMatrix.rowWeights, Fin.cases_succ, Fin.cases_zero]
      using hT i
  have hprod : (e 0 : Real) * v0 ≤
      ((T i : Real) * (e i.succ : Real)) * v0 := by
    calc
      (e 0 : Real) * v0 = R := hzero.symm
      _ = (e i.succ : Real) * (w i / theta) := hsucc
      _ ≤ (e i.succ : Real) * ((T i : Real) * v0) :=
        mul_le_mul_of_nonneg_left htrunc (Nat.cast_nonneg _)
      _ = ((T i : Real) * (e i.succ : Real)) * v0 := by ring
  have hreal : (e 0 : Real) ≤ ((T i * e i.succ : Nat) : Real) := by
    simpa only [Nat.cast_mul] using le_of_mul_le_mul_right hprod hv0
  exact Nat.cast_le.mp hreal

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Real, D < (s : Real) * (R : Real) ∧
      Ideal.span {P : MvPolynomial (Fin (d.m + 1)) Complex |
        P ∈ (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D} =
      (logarithmicCentersIdeal
        (fun j : Fin d.K => fun i =>
          (j.val : Complex) *
            MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
        T e) ^ s := by
  classical
  let w : Fin (d.m + 1) → Real :=
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d))
  let c : Fin d.K → Fin d.m → Complex :=
    fun j i => (j.val : Complex) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i
  let I : Ideal (MvPolynomial (Fin (d.m + 1)) Complex) :=
    logarithmicCentersIdeal c T e
  let J : Ideal (MvPolynomial (Fin (d.m + 1)) Complex) :=
    logarithmicCentersIdeal c (fun _ => e 0) e
  have hw : ∀ i, 0 < w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 < (d.w0 : Real)
      exact d.w0_pos
    · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j
      have hx : (0 : Real) < d.x (j.val + 1) :=
        lt_of_lt_of_le zero_lt_one (d.x_one_le (j.val + 1))
      rw [d.x_log] at hx
      simpa only [MatrixArithmetic.logWeights, finiteDenominators] using hx
  have hcut : ∀ i, e 0 ≤ T i * e i.succ :=
    row_scale_truncation_cutoff d.v0 d.base.theta (R : Real)
      (MatrixArithmetic.logWeights (finiteDenominators d))
      T e d.v0_pos hT hscale
  obtain ⟨delta, hdelta, hdeltaR, N, hrep⟩ :=
    fixedData_canonical_strict_power_representatives nu hnu d R e hR he hscale
  let W : Real := ∑ i, w i
  let B : Real := (d.m : Real) * delta + W
  have hgap : 0 < (R : Real) - delta := sub_pos.mpr hdeltaR
  obtain ⟨s, hs⟩ :=
    exists_nat_gt (max (N : Real) (B / ((R : Real) - delta)))
  have hsN : (N : Real) < (s : Real) :=
    lt_of_le_of_lt (le_max_left _ _) hs
  have hspos : 0 < s := by
    have hsr : (0 : Real) < (s : Real) :=
      lt_of_le_of_lt (Nat.cast_nonneg N) hsN
    exact_mod_cast hsr
  have hNs : N ≤ s := by
    exact_mod_cast (le_of_lt hsN)
  have hratio : B / ((R : Real) - delta) < (s : Real) :=
    lt_of_le_of_lt (le_max_right _ _) hs
  have hbig : B < (s : Real) * ((R : Real) - delta) :=
    (div_lt_iff₀ hgap).mp hratio
  let E : Real := ((s + d.m : Nat) : Real) * delta
  have hE : 0 ≤ E := mul_nonneg (Nat.cast_nonneg _) hdelta.le
  have hstrict : E + W < (s : Real) * (R : Real) := by
    dsimp only [B] at hbig
    dsimp only [E]
    rw [Nat.cast_add]
    nlinarith only [hbig]
  have hcompare : J ^ (s + d.m) ≤ I ^ s :=
    logarithmicCentersIdeal_canonical_power_le c T e he hcut s
  have hbounded :
      ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) Complex,
          P - Q ∈ I ^ s ∧
          ∀ a ∈ Q.support, ∑ i, w i * (a i : Real) ≤ E := by
    intro P
    obtain ⟨Q, hPQ, hQ⟩ :=
      hrep (s + d.m) (hNs.trans (Nat.le_add_right _ _)) P
    exact ⟨Q, hcompare hPQ, hQ⟩
  refine ⟨s, hspos, E + W, hstrict, ?_⟩
  change Ideal.span {P : MvPolynomial (Fin (d.m + 1)) Complex |
    P ∈ I ^ s ∧
    ∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ E + W} = I ^ s
  exact ideal_span_of_bounded_weight_representatives d.m w hw (I ^ s) E hE hbounded