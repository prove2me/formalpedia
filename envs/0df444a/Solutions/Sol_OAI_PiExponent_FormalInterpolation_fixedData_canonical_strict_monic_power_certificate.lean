-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_strict_monic_power_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:38:52.69699+00:00
-- url     : https://prove2.me/submissions/f86b5399-aa03-451c-bb2d-543ff1092caa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_enlarged_logarithmic_interpolation_numerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.Algebra.Order.Archimedean.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

/-
Reduction candidate. The two imported Open children are independent:
one is a numerical perturbation of the degree weights, and one is a
generic critical-radius interpolation theorem for logarithmic ideals.

No strict representative theorem from the existing cyclic chain is used.
The second child retains the substantive geometry. Its intended proof
uses the generic curve-contact inequality, a weighted compactification,
blowup ampleness, ordinary-power jet restriction, and support bounds.
It is not asserted to have been proved or compiler-checked here.

Truncation at e 0 retains degrees strictly below e 0. The second child
uses this exact canonical ideal and its ordinary powers, not its radical
or integral closure. All centers are separated in every nonzero-index
coordinate because the rational-center direction is nonzero there.
-/

theorem bounded_representatives_give_strict_monic_relations
    (m : Nat) (w : Fin (m + 1) → Real) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (B : Real) (hB : 0 ≤ B)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
        P - Q ∈ I ∧
        ∀ a ∈ Q.support, ∑ j, w j * (a j : Real) ≤ B) :
    ∃ N : Fin (m + 1) → Nat,
    ∃ r : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex,
      (∀ i, 0 < N i) ∧
      (∀ i, MvPolynomial.X i ^ N i - r i ∈ I) ∧
      (∀ i, (N i : Real) * w i ≤ B + ∑ j, w j) ∧
      (∀ i, ∀ a ∈ (r i).support,
        ∑ j, w j * (a j : Real) < (N i : Real) * w i) ∧
      (∀ i, ∀ a ∈ (MvPolynomial.X i ^ N i - r i).support,
        ∑ j, w j * (a j : Real) ≤ B + ∑ j, w j) := by
  classical
  let N : Fin (m + 1) → Nat := fun i => ⌊B / w i⌋₊ + 1
  have hNpos : ∀ i, 0 < N i := by
    intro i
    exact Nat.zero_lt_succ _
  have hNlower : ∀ i, B < (N i : Real) * w i := by
    intro i
    apply (div_lt_iff₀ (hw i)).mp
    simpa only [N, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (B / w i))
  have hNupper : ∀ i, (N i : Real) * w i ≤ B + ∑ j, w j := by
    intro i
    have hfloor : (⌊B / w i⌋₊ : Real) * w i ≤ B :=
      (le_div_iff₀ (hw i)).mp (Nat.floor_le (div_nonneg hB (hw i).le))
    have hwi : w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ => (hw j).le) (Finset.mem_univ i)
    calc
      (N i : Real) * w i = (⌊B / w i⌋₊ : Real) * w i + w i := by
        simp only [N, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ B + w i := add_le_add hfloor (le_refl (w i))
      _ ≤ B + ∑ j, w j := add_le_add (le_refl B) hwi
  choose r hrmem hrweight using
    (fun i : Fin (m + 1) => hrep (MvPolynomial.X i ^ N i))
  have hrstrict : ∀ i, ∀ a ∈ (r i).support,
      ∑ j, w j * (a j : Real) < (N i : Real) * w i := by
    intro i a ha
    exact lt_of_le_of_lt (hrweight i a ha) (hNlower i)
  refine ⟨N, r, hNpos, hrmem, hNupper, hrstrict, ?_⟩
  intro i a ha
  rcases Finset.mem_union.mp
      ((MvPolynomial.support_sub (Fin (m + 1))
        (MvPolynomial.X i ^ N i) (r i)) ha) with hpower | hrem
  · have haeq : a = Finsupp.single i (N i) := by
      simpa only [MvPolynomial.support_X_pow, Finset.mem_singleton] using hpower
    subst a
    have hweight :
        (∑ j, w j * ((Finsupp.single i (N i)) j : Real)) =
          (N i : Real) * w i := by
      simp [Finsupp.single_apply, mul_comm]
    rw [hweight]
    exact hNupper i
  · exact (hrstrict i a hrem).le.trans (hNupper i)

/-- Algebraic extraction including the common power and strict slope bound.
This theorem makes no geometric assertion about how to obtain `hrep`. -/
theorem eventual_bounded_representatives_give_strict_monic_power_certificate
    (m : Nat) (w : Fin (m + 1) → Real) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (R delta : Real) (hdelta : 0 ≤ delta) (hdeltaR : delta < R)
    (n0 : Nat)
    (hrep : ∀ n : Nat, n0 ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
          P - Q ∈ I ^ n ∧
          ∀ a ∈ Q.support, ∑ j, w j * (a j : Real) ≤ (n : Real) * delta) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 ≤ D ∧ D < (s : Real) * R ∧
        ∃ N : Fin (m + 1) → Nat,
        ∃ r : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex,
        ∃ f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex,
          (∀ i, 0 < N i) ∧
          (∀ i, f i = MvPolynomial.X i ^ N i - r i) ∧
          (∀ i, f i ∈ I ^ s) ∧
          (∀ i, ∀ a ∈ (f i).support, ∑ j, w j * (a j : Real) ≤ D) ∧
          (∀ i, (N i : Real) * w i ≤ D) ∧
          (∀ i, ∀ a ∈ (r i).support,
            ∑ j, w j * (a j : Real) < (N i : Real) * w i) ∧
          (∀ i, 0 < w i) := by
  classical
  let W : Real := ∑ j, w j
  have hW : 0 ≤ W := Finset.sum_nonneg (fun j _ => (hw j).le)
  obtain ⟨n, hn⟩ := exists_nat_gt (W / (R - delta))
  let s : Nat := max (n0 + 1) n
  have hs : 0 < s :=
    lt_of_lt_of_le (Nat.zero_lt_succ n0) (le_max_left _ _)
  have hs0 : n0 ≤ s :=
    le_trans (Nat.le_succ n0) (le_max_left _ _)
  have hns : (n : Real) ≤ (s : Real) :=
    Nat.cast_le.mpr (le_max_right _ _)
  have hlarge : W < (s : Real) * (R - delta) :=
    (div_lt_iff₀ (sub_pos.mpr hdeltaR)).mp (lt_of_lt_of_le hn hns)
  have hB : 0 ≤ (s : Real) * delta := mul_nonneg (Nat.cast_nonneg _) hdelta
  obtain ⟨N, r, hN, hmem, hupper, hstrict, hsupport⟩ :=
    bounded_representatives_give_strict_monic_relations m w hw (I ^ s)
      ((s : Real) * delta) hB (hrep s hs0)
  refine ⟨s, hs, (s : Real) * delta + W, add_nonneg hB hW, ?_,
    N, r, (fun i => MvPolynomial.X i ^ N i - r i), hN,
    (fun _ => rfl), hmem, hsupport, hupper, hstrict, hw⟩
  calc
    (s : Real) * delta + W < (s : Real) * delta + (s : Real) * (R - delta) :=
      add_lt_add_of_le_of_lt (le_refl ((s : Real) * delta)) hlarge
    _ = (s : Real) * R := by ring

theorem actual_column_weights_positive
    {nu : Real} (d : FixedData nu) :
    ∀ i, 0 < InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 0 < (d.w0 : Real)
    exact d.w0_pos
  · change 0 < (⌈Real.log (d.q j.val)⌉₊ : Real)
    rw [← d.x_log j.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le (j.val + 1))


theorem fixedData_rationalCenters_ne_zero_aux
    {nu : Real} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.rationalCenters
      (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
  change 2 * Complex.I * (d.p i.val : Complex) / (d.q i.val : Complex) ≠ 0
  have hp : (d.p i.val : Complex) ≠ 0 :=
    Int.cast_ne_zero.mpr (d.approximations i.val).2.1
  have hq : (d.q i.val : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (d.approximations i.val).1))
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hp) hq

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 ≤ D ∧ D < (s : Real) * (R : Real) ∧
        ∃ N : Fin (d.m + 1) → Nat,
        ∃ r : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) Complex,
        ∃ f : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) Complex,
          (∀ i, 0 < N i) ∧
          (∀ i, f i = MvPolynomial.X i ^ N i - r i) ∧
          (∀ i, f i ∈ (logarithmicCentersIdeal
            (fun j : Fin d.K => fun i =>
              (j.val : Complex) *
                MatrixArithmetic.rationalCenters
                  (finiteNumerators d) (finiteDenominators d) i)
            (fun _ => e 0) e) ^ s) ∧
          (∀ i, ∀ a ∈ (f i).support,
            ∑ j, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                (a j : Real) ≤ D) ∧
          (∀ i, (N i : Real) * InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i ≤ D) ∧
          (∀ i, ∀ a ∈ (r i).support,
            ∑ j, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                (a j : Real) <
              (N i : Real) * InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
          (∀ i, 0 < InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) := by
  classical
  obtain ⟨t, ht, w, v, hw, hv, hnum⟩ :=
    OAI.PiExponent.FormalInterpolation.fixedData_enlarged_logarithmic_interpolation_numerics d
  let c : Fin d.K → Fin d.m → Complex :=
    fun j i => (j.val : Complex) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i
  have hc : ∀ i : Fin d.m, Function.Injective (fun j : Fin d.K => c j i) := by
    intro i j k hjk
    have hval : (j.val : Complex) = (k.val : Complex) :=
      mul_right_cancel₀ (fixedData_rationalCenters_ne_zero_aux d i) hjk
    exact Fin.ext (Nat.cast_injective hval)
  have hscale' : ∀ i, (R : Real) = (e i : Real) * (v i : Real) := by
    intro i
    rw [hv i]
    exact hscale i
  obtain ⟨n0, hrep⟩ :=
    OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
      c hc w v d.sigma hnum R e hR he hscale'
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hRR : 0 < (R : Real) := Rat.cast_pos.mpr hR
  apply eventual_bounded_representatives_give_strict_monic_power_certificate
    d.m
    (InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)))
    (actual_column_weights_positive d)
    (logarithmicCentersIdeal c (fun _ => e 0) e)
    (R : Real) ((R : Real) / t)
    (div_nonneg hRR.le ht0.le) (div_lt_self hRR ht) n0
  intro n hn P
  obtain ⟨Q, hPQ, hQ⟩ := hrep n hn P
  refine ⟨Q, hPQ, ?_⟩
  intro a ha
  have hweight :
      (∑ j, InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) j *
          (a j : Real)) * t =
        ∑ j, (w j : Real) * (a j : Real) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j]
    ring
  have hbound :
      (∑ j, InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) j *
          (a j : Real)) * t ≤ (n : Real) * (R : Real) :=
    hweight.trans_le (hQ a ha)
  have hdiv := (le_div_iff₀ ht0).mpr hbound
  simpa only [mul_div_assoc] using hdiv
