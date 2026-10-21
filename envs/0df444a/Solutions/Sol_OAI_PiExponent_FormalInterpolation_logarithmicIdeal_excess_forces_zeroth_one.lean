-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicIdeal_excess_forces_zeroth_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T03:51:47.812001+00:00
-- url     : https://prove2.me/submissions/757c9606-0133-4ea9-84e9-bd77d889dad9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_cofinal_logarithmic_auxiliary_polynomial
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_word_ideal_contact_estimates
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_scaled_divisor_comparison
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_logarithmic_word_rigidity
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

private theorem logarithmic_solution_pole_nonneg
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (w : Fin d → Rat) :
    0 ≤ polynomialCurvePole nu x w := by
  classical
  unfold polynomialCurvePole
  exact Finset.le_sup'
    (fun i : Option (Fin d) => i.elim (0 : Real) (fun j =>
      -(polynomialCurveOrder nu (x j) : Real) / (w j : Real)))
    (Finset.mem_univ (none : Option (Fin d)))

private theorem logarithmic_solution_contact_zero
    {m K : Nat} (c : Fin K → Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat)
    {E : Type} [Field E] [Algebra Complex E] (x : Fin (m + 1) → E)
    (a : Complex) (ha : x 0 = algebraMap Complex E a) (ha1 : a ≠ 1)
    (nu : PolynomialCurvePlace E) :
    polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) = 0 := by
  classical
  let q : MvPolynomial (Fin (m + 1)) Complex := (MvPolynomial.X 0 - 1) ^ e 0
  let f : MvPolynomial (Fin (m + 1)) Complex := ∏ _j : Fin K, q
  have hf : f ∈ logarithmicCentersIdeal c T e := by
    change (∏ _j : Fin K, q) ∈ ∏ j : Fin K, logarithmicCenterIdeal (c j) T e
    apply Ideal.prod_mem_prod
    intro j hj
    change q ∈ Ideal.span
      (Set.range (fun i => logarithmicCoordinate (c j) T i ^ e i))
    exact Ideal.subset_span ⟨0, rfl⟩
  let b : Complex := ∏ _j : Fin K, (a - 1) ^ e 0
  have hb : b ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun j _ => pow_ne_zero _ (sub_ne_zero.mpr ha1))
  have hfval : MvPolynomial.aeval x f = algebraMap Complex E b := by
    simp only [f, b, q, map_prod, map_pow, map_sub, MvPolynomial.aeval_X, ha, map_one]
  unfold polynomialCurveIdealContact
  split
  · apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    refine ⟨f, hf, ?_⟩
    change nu.1 (MvPolynomial.aeval x f) = 0
    rw [hfval]
    exact nu.2.1 b hb
  · rfl

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hvolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
        (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hexcess :
      (R : Real) * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
        (1 + (sigma : Real)) *
          (∑ᶠ nu : PolynomialCurvePlace E,
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    x 0 = 1 := by
  classical
  have hRR : (0 : Real) < (R : Real) := Rat.cast_pos.mpr hR
  have hpole :
      0 ≤ ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w :=
    finsum_nonneg (fun nu => logarithmic_solution_pole_nonneg nu x w)
  have hmass :
      0 ≤ ∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) :=
    finsum_nonneg (fun _ => Nat.cast_nonneg _)
  obtain ⟨N₀, hrigid⟩ :=
    eventual_logarithmic_word_rigidity hm w v sigma hsigma hw hv hseparated
      E htrdeg x hgen
  obtain ⟨N, hNN, hN, F, hF0, hF, hjet⟩ :=
    cofinal_logarithmic_auxiliary_polynomial c w v sigma hm hK hsigma hw hv hvolume N₀
  have hNR : (0 : Real) < (N : Real) := Nat.cast_pos.mpr hN
  have hwords : ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
      MvPolynomial.aeval x (logarithmicFrameWord word F) = 0 := by
    intro word hword
    have hM : 0 ≤ (1 + 3 * (sigma : Real)) * (N : Real) :=
      mul_nonneg (by linarith) hNR.le
    have hwordM :
        logarithmicFrameCost v word ≤ (1 + 3 * (sigma : Real)) * (N : Real) := by
      exact hword.trans (mul_le_mul_of_nonneg_right (by linarith) hNR.le)
    have hest :=
      logarithmic_word_ideal_contact_estimates c hc hm hK w v hw hv R e hR he hscale
        E htrdeg x hgen (N : Real) ((1 + 3 * (sigma : Real)) * (N : Real))
        hNR.le hM F hF hjet word hwordM
    by_contra hne
    have hdiv :=
      polynomial_curve_scaled_divisor_comparison E htrdeg x hgen w hw (N : Real)
        hNR.le (logarithmicFrameWord word F) hest.1 hne
        ((1 + 2 * (sigma : Real)) * (N : Real)) (R : Real)
        (mul_pos (by linarith) hNR) hRR
        (fun nu : PolynomialCurvePlace E =>
          (polynomialCurveIdealContact nu x
            (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))
        (fun _ => Nat.cast_nonneg _) (by
          intro nu hnu
          have hret :
              (1 + 2 * (sigma : Real)) * (N : Real) ≤
                (1 + 3 * (sigma : Real)) * (N : Real) -
                  logarithmicFrameCost v word := by nlinarith only [hword]
          exact (mul_le_mul_of_nonneg_right hret hnu.le).trans (hest.2 nu hnu hne))
    have hweaken :
        ((1 + (sigma : Real)) * (N : Real)) *
            (∑ᶠ nu : PolynomialCurvePlace E,
              (polynomialCurveIdealContact nu x
                (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) ≤
          ((1 + 2 * (sigma : Real)) * (N : Real)) *
            (∑ᶠ nu : PolynomialCurvePlace E,
              (polynomialCurveIdealContact nu x
                (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hNR.le) hmass
    have hexN := mul_lt_mul_of_pos_left hexcess hNR
    nlinarith only [hdiv, hweaken, hexN]
  obtain ⟨a, ha⟩ := hrigid N hNN hN F hF0 hF hwords
  by_contra hx
  have ha1 : a ≠ 1 := by
    intro haone
    apply hx
    simpa only [haone, map_one] using ha
  have hzero : ∀ nu : PolynomialCurvePlace E,
      polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) = 0 :=
    fun nu => logarithmic_solution_contact_zero c (fun _ => e 0) e x a ha ha1 nu
  have hsumzero :
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) = 0 := by
    simp only [hzero, Nat.cast_zero, finsum_zero]
  rw [hsumzero, mul_zero] at hexcess
  exact (not_lt_of_ge (mul_nonneg hRR.le hpole)) hexcess
