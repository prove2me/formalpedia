-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:50:10.402841+00:00
-- url     : https://prove2.me/submissions/f1a0fcdf-7590-4ac6-b6ac-3a933b310a7e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

private theorem aeval_coord_sub_const
    {m : Nat} {E : Type} [Field E] [Algebra Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (c : Fin m → Complex) (T : Fin m → Nat) (i : Fin m) :
    MvPolynomial.aeval x (logarithmicCoordinate c T i.succ) =
      x i.succ - algebraMap Complex E (c i) := by
  have htrunc0 : (InterpolationMatrix.truncatedLog (T i)).coeff 0 = 0 := by
    simp [InterpolationMatrix.truncatedLog, PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  have haeval0 :
      Polynomial.aeval (0 : E) (InterpolationMatrix.truncatedLog (T i)) = 0 := by
    have h :=
      Polynomial.coeff_zero_eq_aeval_zero' (A := E) (InterpolationMatrix.truncatedLog (T i))
    simpa [htrunc0, map_zero] using h.symm
  set X0m1 : MvPolynomial (Fin (m + 1)) Complex :=
    MvPolynomial.X (0 : Fin (m + 1)) - (1 : MvPolynomial (Fin (m + 1)) Complex)
  have hx01 : MvPolynomial.aeval x X0m1 = 0 := by simp [X0m1, hfibre]
  have hxcoord :
      logarithmicCoordinate c T i.succ =
        MvPolynomial.X i.succ - MvPolynomial.C (c i) -
          Polynomial.aeval X0m1 (InterpolationMatrix.truncatedLog (T i)) := by
    simp [logarithmicCoordinate, X0m1]
  rw [hxcoord, map_sub, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have hlog :
      MvPolynomial.aeval x
          (Polynomial.aeval X0m1 (InterpolationMatrix.truncatedLog (T i))) = 0 := by
    rw [← Polynomial.aeval_algHom_apply (MvPolynomial.aeval (R := Complex) x) X0m1 _]
    rw [hx01, haeval0]
  rw [hlog, sub_zero]

-- Cleaner specialized helper:
private theorem addValuation_map_prod_fin
    {E : Type} [Field E] (v : AddValuation E (WithTop Int))
    {n : Nat} (f : Fin n → E) :
    v (∏ i : Fin n, f i) = ∑ i : Fin n, v (f i) := by
  classical
  refine Finset.univ.induction_on (motive := fun s =>
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i)) ?empty ?insert
  · simp [AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (j : Fin K) (hj : c j i0 = a) (nu : PolynomialCurvePlace E) :
    (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real) ≤
      (e k.succ : Real) *
        max (polynomialCurveOrder nu
          (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by
  classical
  set I := logarithmicCentersIdeal c T e
  set diff : E := x k.succ - algebraMap Complex E (c j k)
  by_cases h_aff : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · have hdiff_ne : diff ≠ 0 := by
      intro h0
      have hxeq : x k.succ = algebraMap Complex E (c j k) := sub_eq_zero.mp h0
      have : IsAlgebraic Complex (x k.succ) := by
        rw [hxeq]; exact isAlgebraic_algebraMap _
      exact hk this
    have hnu_diff_ge : (0 : WithTop Int) ≤ nu.1 diff := by
      have h1 : (0 : WithTop Int) ≤ nu.1 (x k.succ) := h_aff _
      have h2 : (0 : WithTop Int) ≤ nu.1 (-algebraMap Complex E (c j k)) := by
        by_cases hz : c j k = 0
        · simp [hz, map_zero, neg_zero, AddValuation.map_zero]
        · have := nu.property.1 _ hz
          simpa [AddValuation.map_neg, this]
      have hmin := AddValuation.map_add (nu.1) (x k.succ) (-algebraMap Complex E (c j k))
      -- hmin : min _ _ ≤ nu (x + -c)
      refine le_trans (le_min h1 h2) ?_
      simpa [diff, sub_eq_add_neg] using hmin
    have hnu_diff_ne_top : nu.1 diff ≠ ⊤ := (AddValuation.ne_top_iff (nu.1)).2 hdiff_ne
    have hnu_diff_coe :
        nu.1 diff = ↑(polynomialCurveOrder nu diff) := by
      simp only [polynomialCurveOrder]
      exact (WithTop.coe_untop₀_of_ne_top hnu_diff_ne_top).symm
    have hord_nonneg : 0 ≤ polynomialCurveOrder nu diff := by
      have := hnu_diff_ge
      rw [hnu_diff_coe] at this
      exact WithTop.coe_le_coe.mp this
    have hmax :
        max (polynomialCurveOrder nu diff : ℝ) 0 =
          (polynomialCurveOrder nu diff : ℝ) :=
      max_eq_left (by exact_mod_cast hord_nonneg)
    set f : Fin K → MvPolynomial (Fin (m + 1)) Complex := fun ℓ =>
      if hℓ : ℓ = j then
        logarithmicCoordinate (c j) T k.succ ^ e k.succ
      else
        logarithmicCoordinate (c ℓ) T i0.succ ^ e i0.succ
    have hfmem : ∀ ℓ, f ℓ ∈ logarithmicCenterIdeal (c ℓ) T e := by
      intro ℓ
      dsimp [f]; split_ifs with hℓ
      · subst hℓ; exact Ideal.subset_span ⟨k.succ, rfl⟩
      · exact Ideal.subset_span ⟨i0.succ, rfl⟩
    set G := ∏ ℓ : Fin K, f ℓ
    have hGmem : G ∈ I := by
      simpa [G, I, logarithmicCentersIdeal] using
        Ideal.prod_mem_prod (fun ℓ _ => hfmem ℓ)
    have hcoord_k :
        MvPolynomial.aeval x (logarithmicCoordinate (c j) T k.succ) = diff := by
      simpa [diff] using aeval_coord_sub_const (E := E) x hfibre (c j) T k
    have hcoord_i0' : ∀ ℓ : Fin K,
        MvPolynomial.aeval x (logarithmicCoordinate (c ℓ) T i0.succ) =
          algebraMap Complex E (a - c ℓ i0) := by
      intro ℓ
      rw [aeval_coord_sub_const (E := E) x hfibre (c ℓ) T i0, ha, ← map_sub]
    have hfeval : ∀ ℓ,
        MvPolynomial.aeval x (f ℓ) =
          if ℓ = j then diff ^ (e k.succ)
          else algebraMap Complex E ((a - c ℓ i0) ^ (e i0.succ)) := by
      intro ℓ
      dsimp [f]; split_ifs with hℓ
      · subst hℓ; rw [map_pow, hcoord_k]
      · rw [map_pow, hcoord_i0', ← map_pow]
    have hother_ne : ∀ ℓ : Fin K, ℓ ≠ j → a - c ℓ i0 ≠ 0 := by
      intro ℓ hℓ hz
      exact hℓ ((hc i0) (by simpa [hj] using (sub_eq_zero.mp hz).symm))
    have hordG :
        nu.1 (MvPolynomial.aeval x G) =
          ↑((e k.succ : ℤ) * polynomialCurveOrder nu diff) := by
      simp only [G, map_prod]
      rw [addValuation_map_prod_fin (nu.1)]
      have hterm : ∀ ℓ,
          nu.1 (MvPolynomial.aeval x (f ℓ)) =
            if ℓ = j then ↑((e k.succ : ℤ) * polynomialCurveOrder nu diff)
            else (0 : WithTop ℤ) := by
        intro ℓ
        rw [hfeval]
        split_ifs with hℓ
        · rw [AddValuation.map_pow, hnu_diff_coe, ← WithTop.coe_nsmul, nsmul_eq_mul]
        · have hne : a - c ℓ i0 ≠ 0 := hother_ne ℓ hℓ
          by_cases he : e i0.succ = 0
          · simp [he, pow_zero, AddValuation.map_one]
          · exact nu.property.1 _ (pow_ne_zero _ hne)
      simp_rw [hterm]
      -- ∑_ℓ (if ℓ=j then val else 0) = val
      have :
          (∑ ℓ : Fin K,
              (if ℓ = j then (↑((e k.succ : ℤ) * polynomialCurveOrder nu diff) : WithTop ℤ)
                else 0)) =
            ↑((e k.succ : ℤ) * polynomialCurveOrder nu diff) := by
        rw [Fintype.sum_ite_eq' j]
      exact this
    -- Contact ≤ e * ord as naturals.
    set nOrd : ℕ := (polynomialCurveOrder nu diff).toNat
    have hto : (nOrd : ℤ) = polynomialCurveOrder nu diff :=
      Int.toNat_of_nonneg hord_nonneg
    have hn_val :
        nu.1 (MvPolynomial.aeval x G) = ↑(e k.succ * nOrd) := by
      rw [hordG, ← hto]; push_cast; rfl
    have hcontact_le :
        polynomialCurveIdealContact nu x I ≤ e k.succ * nOrd := by
      rw [polynomialCurveIdealContact, if_pos h_aff]
      exact Nat.sInf_le ⟨G, hGmem, hn_val⟩
    have : (polynomialCurveIdealContact nu x I : ℝ) ≤
        (e k.succ : ℝ) * (polynomialCurveOrder nu diff : ℝ) := by
      have htoR : (nOrd : ℝ) = (polynomialCurveOrder nu diff : ℝ) := by
        exact_mod_cast hto
      calc
        (polynomialCurveIdealContact nu x I : ℝ)
            ≤ ((e k.succ * nOrd : ℕ) : ℝ) := by exact_mod_cast hcontact_le
        _ = (e k.succ : ℝ) * (nOrd : ℝ) := by push_cast; rfl
        _ = (e k.succ : ℝ) * (polynomialCurveOrder nu diff : ℝ) := by rw [htoR]
    simpa [I, diff, hmax] using this
  · have hz : polynomialCurveIdealContact nu x I = 0 := by
      simp only [polynomialCurveIdealContact, I, if_neg h_aff]
    simp [hz]
    exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
