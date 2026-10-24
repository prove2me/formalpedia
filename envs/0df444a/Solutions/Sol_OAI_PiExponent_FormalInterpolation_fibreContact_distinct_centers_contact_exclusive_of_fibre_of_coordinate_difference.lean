-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:10:18.638864+00:00
-- url     : https://prove2.me/submissions/16353f26-47f6-4159-a0c9-d8a0769ac1b4

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

namespace PXFC1

lemma tl_zero (T : ℕ) {E : Type} [Field E] [Algebra Complex E] :
    Polynomial.aeval (0 : E) (OAI.PiExponent.InterpolationMatrix.truncatedLog T) = 0 := by
  rw [← Polynomial.coeff_zero_eq_aeval_zero', OAI.PiExponent.InterpolationMatrix.truncatedLog,
    PowerSeries.coeff_trunc]
  split_ifs
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_log, map_zero]
  · exact map_zero _

/-- If the contact is positive (in the affine branch), no element of `I` has valuation `0`. -/
lemma no_unit {d : ℕ} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (I : Ideal (MvPolynomial (Fin d) Complex))
    (hpos : 0 < polynomialCurveIdealContact nu x I) (g : MvPolynomial (Fin d) Complex) (hg : g ∈ I) :
    nu.1 (MvPolynomial.aeval x g) ≠ 0 := by
  classical
  intro h0
  unfold polynomialCurveIdealContact at hpos
  split_ifs at hpos with hc
  · have : sInf {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
        f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} ≤ 0 :=
      Nat.sInf_le ⟨g, hg, by rw [h0]; rfl⟩
    omega
  · exact lt_irrefl 0 hpos

lemma cond {d : ℕ} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (I : Ideal (MvPolynomial (Fin d) Complex))
    (hpos : 0 < polynomialCurveIdealContact nu x I) : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i) := by
  classical
  by_contra hc
  unfold polynomialCurveIdealContact at hpos
  rw [if_neg hc] at hpos
  exact lt_irrefl 0 hpos

lemma val_const_nonneg {E : Type} [Field E] [Algebra Complex E] (nu : PolynomialCurvePlace E) (b : ℂ) :
    (0 : WithTop Int) ≤ nu.1 (algebraMap Complex E b) := by
  by_cases hb : b = 0
  · rw [hb, map_zero, AddValuation.map_zero]; exact le_top
  · rw [nu.2.1 b hb]

/-- positive valuation of the shifted coordinate for one center -/
lemma coord_pos {m : ℕ} (c : Fin m → Complex) (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hpos : 0 < polynomialCurveIdealContact nu x (logarithmicCenterIdeal c (fun _ => e 0) e))
    (i : Fin m) :
    (0 : WithTop Int) < nu.1 (x i.succ - algebraMap Complex E (c i)) := by
  have hc := cond nu x _ hpos
  set y := x i.succ - algebraMap Complex E (c i) with hy
  have hge : (0 : WithTop Int) ≤ nu.1 y :=
    le_trans (le_min (hc i.succ) (val_const_nonneg nu (c i))) (AddValuation.map_sub _ _ _)
  have hgen : (logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ ∈
      logarithmicCenterIdeal c (fun _ => e 0) e :=
    Ideal.subset_span ⟨i.succ, rfl⟩
  have hev : MvPolynomial.aeval x ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ) = y ^ e i.succ := by
    rw [map_pow]
    congr 1
    simp only [logarithmicCoordinate, Fin.cases_succ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [← Polynomial.aeval_algHom_apply, map_sub, MvPolynomial.aeval_X, map_one, hfibre, sub_self,
      tl_zero, sub_zero]
  have hne := no_unit nu x _ hpos _ hgen
  rw [hev, AddValuation.map_pow] at hne
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso; apply hne; rw [← h, smul_zero]

end PXFC1

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hfibre : x 0 = 1)
    (j k : Fin K) (hjk : j ≠ k)
    (hdiff : ∃ i : Fin m, c j i ≠ c k i) :
    ¬ (0 < polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
       0 < polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by
  rintro ⟨hj, hk⟩
  obtain ⟨i, hi⟩ := hdiff
  have pj := PXFC1.coord_pos (c j) e he nu x hfibre hj i
  have pk := PXFC1.coord_pos (c k) e he nu x hfibre hk i
  have hsub : (x i.succ - algebraMap Complex E (c k i)) - (x i.succ - algebraMap Complex E (c j i))
      = algebraMap Complex E (c j i - c k i) := by
    rw [map_sub]; ring
  have h1 := AddValuation.map_sub nu.1 (x i.succ - algebraMap Complex E (c k i))
    (x i.succ - algebraMap Complex E (c j i))
  rw [hsub, nu.2.1 _ (sub_ne_zero.2 hi)] at h1
  exact absurd (lt_of_lt_of_le (lt_min pk pj) h1) (lt_irrefl 0)
