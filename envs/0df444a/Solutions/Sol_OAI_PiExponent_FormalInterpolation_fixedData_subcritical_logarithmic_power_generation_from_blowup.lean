-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation_from_blowup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T20:40:44.028526+00:00
-- url     : https://prove2.me/submissions/e73e0ebd-c9a6-4c31-beac-17d7f597d7bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_enlarged_logarithmic_interpolation_numerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_span_of_bounded_weight_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_contact_cutoff_invariance
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_weighted_curve_contact_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_implies_eventual_weighted_generation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

/-
The scale equation is indexed by Fin (d.m + 1), not Fin d.m.
The only new child is the placewise cutoff comparison. The two geometric
children retain their existing platform identities and exact declarations.
The final bounded-generation step uses an existing proved algebra lemma.
-/
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
      ∃ S : Finset (MvPolynomial (Fin (d.m + 1)) Complex),
        Ideal.span (S : Set (MvPolynomial (Fin (d.m + 1)) Complex)) =
          (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ P ∈ S, ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D := by
  classical
  let c : Fin d.K → Fin d.m → Complex := fun j i =>
    (j.val : Complex) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i
  let I := logarithmicCentersIdeal c T e
  obtain ⟨t, ht, w, v, hw, hv, hnum⟩ :=
    fixedData_enlarged_logarithmic_interpolation_numerics d
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hscalev : ∀ i, (R : Real) = (e i : Real) * (v i : Real) := by
    intro i
    rw [hv i]
    exact hscale i
  have hTv : ∀ i, (v i.succ : Real) ≤ (T i : Real) * (v 0 : Real) := by
    intro i
    rw [hv i.succ, hv 0]
    exact hT i
  have hc : ∀ i : Fin d.m, Function.Injective (fun j : Fin d.K => c j i) := by
    intro i
    have hp : (d.p i.val : Complex) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hqnat : d.q i.val ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : Nat) < 2)
        (d.approximations i.val).1)
    have hq : (d.q i.val : Complex) ≠ 0 := by
      exact_mod_cast hqnat
    have hr : MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
      change 2 * Complex.I * (d.p i.val : Complex) / (d.q i.val : Complex) ≠ 0
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
    intro j k hjk
    have hval : (j.val : Complex) = (k.val : Complex) :=
      mul_right_cancel₀ hr hjk
    apply Fin.ext
    exact_mod_cast hval
  have hdist : ∀ j k : Fin d.K, j ≠ k → c j ≠ c k := by
    intro j k hjk hck
    let i : Fin d.m := ⟨0, lt_of_lt_of_le Nat.zero_lt_one d.m_pos⟩
    exact hjk (hc i (congrFun hck i))
  have hfinite : Module.Finite Complex
      (MvPolynomial (Fin (d.m + 1)) Complex ⧸ I) :=
    logarithmicCentersIdeal_finiteColength c T e he hdist
  let rho : Rat := R / (1 + d.sigma)
  have hcanonical : WeightedIdealCurveBound
      (logarithmicCentersIdeal c (fun _ => e 0) e) w rho :=
    logarithmicCentersIdeal_weighted_curve_contact_bound
      c hc w v d.sigma hnum R e hR he hscalev
  have hcurve : WeightedIdealCurveBound I w rho := by
    intro E _ _ _ htrdeg x hgen
    change (∑ᶠ b : PolynomialCurvePlace E,
        (polynomialCurveIdealContact b x (logarithmicCentersIdeal c T e) : Real)) ≤
      (rho : Real) * ∑ᶠ b : PolynomialCurvePlace E, polynomialCurvePole b x w
    simpa only [logarithmicCentersIdeal_contact_cutoff_invariance
      c v hnum.jet_pos R e hR he hscalev T hTv E] using
      hcanonical E htrdeg x hgen
  have hsigma : 0 < d.sigma := by
    exact_mod_cast hnum.sigma_pos
  have hrhopos : 0 < rho := by
    dsimp [rho]
    exact div_pos hR (by linarith)
  have hrhoR : rho < R := by
    dsimp [rho]
    exact div_lt_self hR (by linarith)
  let delta : Rat := (rho + R) / 2
  have hrhodelta : rho < delta := by
    dsimp [delta]
    linarith
  have hdeltapos : 0 < delta := lt_trans hrhopos hrhodelta
  have hdeltaR : delta < R := by
    dsimp [delta]
    linarith
  have heps : 0 < (delta : Real) - (rho : Real) := by
    apply sub_pos.mpr
    exact_mod_cast hrhodelta
  obtain ⟨N, hN⟩ :=
    weightedIdealCurveBound_implies_eventual_weighted_generation
      I hfinite w hnum.degree_pos rho hrhopos.le hcurve
      ((delta : Real) - (rho : Real)) heps
  have hbudget : (rho : Real) + ((delta : Real) - (rho : Real)) =
      (delta : Real) := by ring
  have hrep : ∀ n : Nat, N ≤ n →
      ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
      ∃ Q : MvPolynomial (Fin (d.m + 1)) Complex,
        P - Q ∈ I ^ n ∧
        ∀ a ∈ Q.support, ∑ i, (w i : Real) * (a i : Real) ≤
          (n : Real) * (delta : Real) := by
    intro n hn P
    obtain ⟨Q, hQ⟩ := hN n hn (Ideal.Quotient.mk (I ^ n) P)
    refine ⟨Q.1, (Ideal.Quotient.eq).mp hQ.symm, ?_⟩
    intro a ha
    simpa only [hbudget] using Q.2 a ha
  let W : Real := ∑ i, (w i : Real)
  have hgap : 0 < (R : Real) - (delta : Real) := by
    apply sub_pos.mpr
    exact_mod_cast hdeltaR
  obtain ⟨s, hs⟩ := exists_nat_gt
    (max (N : Real) (W / ((R : Real) - (delta : Real))))
  have hNsreal : (N : Real) < (s : Real) :=
    lt_of_le_of_lt (le_max_left _ _) hs
  have hNs : N ≤ s := by exact_mod_cast hNsreal.le
  have hspos : 0 < s := by
    have hh : (0 : Real) < (s : Real) :=
      lt_of_le_of_lt (Nat.cast_nonneg N) hNsreal
    exact_mod_cast hh
  have hlarge : W < (s : Real) * ((R : Real) - (delta : Real)) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_right _ _) hs)
  let D : Real := (s : Real) * (delta : Real) + W
  have hDR : D < (s : Real) * (R : Real) := by
    dsimp [D]
    nlinarith only [hlarge]
  have hnonneg : 0 ≤ (s : Real) * (delta : Real) := by
    apply mul_nonneg (Nat.cast_nonneg s)
    exact_mod_cast hdeltapos.le
  let B : Set (MvPolynomial (Fin (d.m + 1)) Complex) :=
    {P | P ∈ I ^ s ∧
      ∀ a ∈ P.support, ∑ i, (w i : Real) * (a i : Real) ≤ D}
  have hspan : Ideal.span B = I ^ s :=
    ideal_span_of_bounded_weight_representatives d.m
      (fun i => (w i : Real)) hnum.degree_pos (I ^ s)
      ((s : Real) * (delta : Real)) hnonneg (hrep s hNs)
  have hfg : (Ideal.span B).FG := IsNoetherian.noetherian _
  obtain ⟨S, hSB, hSS⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset B).mp hfg
  have hSI : Ideal.span (S : Set (MvPolynomial (Fin (d.m + 1)) Complex)) =
      I ^ s := hSS.symm.trans hspan
  refine ⟨s, hspos, D / t, ?_, S, hSI, ?_⟩
  · apply (div_lt_iff₀ htpos).mpr
    have hsR : 0 < (s : Real) * (R : Real) := by
      apply mul_pos
      · exact_mod_cast hspos
      · exact_mod_cast hR
    have hh := mul_nonneg hsR.le (sub_nonneg.mpr ht.le)
    nlinarith only [hDR, hh]
  · intro P hP a ha
    have hPw : ∑ i, (w i : Real) * (a i : Real) ≤ D :=
      (hSB hP).2 a ha
    apply (le_div_iff₀ htpos).mpr
    calc
      (∑ i, InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real)) * t =
          t * (∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real)) :=
        mul_comm _ _
      _ = ∑ i, (w i : Real) * (a i : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hw i]
        ring
      _ ≤ D := hPw
