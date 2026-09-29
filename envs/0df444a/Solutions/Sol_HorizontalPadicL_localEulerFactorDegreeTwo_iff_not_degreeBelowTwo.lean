-- Prove2me | solution 1 for HorizontalPadicL.localEulerFactorDegreeTwo_iff_not_degreeBelowTwo
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T20:07:40.665705+00:00
-- url     : https://prove2.me/submissions/6bd859b3-8dd4-4a43-a2da-d49e522c430c

import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms

open IsDedekindDomain NumberField ArithmeticFunction PowerSeries

namespace EulerAux

/-- Convolving with a function that restricts to `δ` on the powers of `p` leaves the values at
powers of `p` unchanged. -/
lemma mul_apply_prime_pow_of_delta {p : ℕ} (hp : p.Prime) (A B : ArithmeticFunction ℤ)
    (hB : ∀ j, B (p ^ j) = if j = 0 then 1 else 0) (k : ℕ) :
    (A * B) (p ^ k) = A (p ^ k) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => A a * B b), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  rw [Finset.sum_eq_single k]
  · simp only [Function.Embedding.coeFn_mk]
    rw [Nat.div_self (pow_pos hp.pos k)]
    have h0 := hB 0
    rw [pow_zero] at h0
    rw [h0, if_pos rfl, mul_one]
  · intro i hi hik
    simp only [Function.Embedding.coeFn_mk]
    have hik' : i < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hik
    rw [Nat.pow_div hik'.le hp.pos, hB, if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h

lemma prod_delta {ι : Type*} {p : ℕ} (hp : p.Prime) (t : Finset ι) (F : ι → ArithmeticFunction ℤ)
    (hF : ∀ i ∈ t, ∀ j, F i (p ^ j) = if j = 0 then 1 else 0) :
    ∀ j, (∏ i ∈ t, F i) (p ^ j) = if j = 0 then 1 else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro j
    simp [ArithmeticFunction.one_apply, hp.ne_one]
  | insert a t ha ih =>
    intro j
    rw [Finset.prod_insert ha, mul_apply_prime_pow_of_delta hp _ _
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))]
    exact hF a (Finset.mem_insert_self a t) j

noncomputable abbrev P (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.primesEquiv v

lemma card_residue (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = P v := by
  have : Fact (Nat.Prime (P v)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
        PadicInt.residueField).toEquiv]
  simp

instance northcott_card : Northcott (fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))) where
  finite_le b := by
    simp_rw [card_residue]
    exact (Set.finite_Iic b).preimage
      ((Subtype.val_injective.comp (Rat.HeightOneSpectrum.primesEquiv).injective).injOn)

/-- The local power series of `E` at the place `v`. -/
noncomputable abbrev Fv (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : PowerSeries ℤ :=
  (E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)

lemma constantCoeff_Fv (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    constantCoeff (Fv E v) = 1 := by
  simp [Fv, WeierstrassCurve.localPowerSeries, constantCoeff_invOfUnit]

lemma factor_delta (E : WeierstrassCurve ℚ) (v w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) (j : ℕ) :
    ofPowerSeries (Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ))) (Fv E w)
      (P v ^ j) = if j = 0 then 1 else 0 := by
  have hpv : (P v).Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  have hpw : (P w).Prime := (Rat.HeightOneSpectrum.primesEquiv w).2
  rw [card_residue]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [constantCoeff_Fv E w]
  · rw [if_neg hj.ne', ofPowerSeries_apply hpw.one_lt, Function.extend_apply']
    · rfl
    rintro ⟨i, hi⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero] at hi
      exact absurd hi.symm (Nat.one_lt_pow hj.ne' hpv.one_lt).ne'
    · have hdvd : P w ∣ P v ^ j := hi ▸ dvd_pow_self (P w) hi0.ne'
      have heq : P w = P v := (Nat.prime_dvd_prime_iff_eq hpw hpv).mp (hpw.dvd_of_dvd_pow hdvd)
      exact hw ((Rat.HeightOneSpectrum.primesEquiv).injective (Subtype.ext heq))

lemma LFunction_prime_pow (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    E.LFunction (P v ^ k) = coeff k (Fv E v) := by
  have hp : (P v).Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  obtain ⟨s, hs1, hs2⟩ := ((tendsTo_eulerProduct_ofPowerSeries
    (fun w : HeightOneSpectrum (𝓞 ℚ) => Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)))
    (Fv E) (constantCoeff_Fv E) (P v ^ k)).and (Filter.eventually_ge_atTop {v})).exists
  unfold WeierstrassCurve.LFunction
  simp only [WeierstrassCurve.localEulerFactor] at hs1 ⊢
  rw [← hs1]
  have hv : v ∈ s := hs2 (Finset.mem_singleton_self v)
  classical
  rw [← Finset.mul_prod_erase s _ hv, mul_apply_prime_pow_of_delta hp]
  · rw [card_residue, ofPowerSeries_apply_pow hp.one_lt]
  · exact prod_delta hp _ _ fun w hw j => factor_delta E v w (Finset.ne_of_mem_erase hw) j


lemma Fv_mul (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) : PowerSeries ℤ)
      * Fv E v = 1 := by
  unfold Fv WeierstrassCurve.localPowerSeries
  apply mul_invOfUnit
  simp only [WeierstrassCurve.localPolynomial]
  split_ifs <;> simp

lemma rec_linear (c : ℤ) (F : PowerSeries ℤ)
    (h : ((1 - Polynomial.C c * Polynomial.X : Polynomial ℤ) : PowerSeries ℤ) * F = 1) (n : ℕ) :
    coeff (n + 1) F = c * coeff n F := by
  have := congrArg (coeff (n + 1)) h
  simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul,
    coeff_one, Nat.succ_ne_zero, if_false] at this
  linarith

lemma rec_quad (a q : ℤ) (F : PowerSeries ℤ)
    (h : ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℤ) :
      PowerSeries ℤ) * F = 1) :
    coeff 1 F = a * coeff 0 F ∧ ∀ r, coeff (r + 2) F = a * coeff (r + 1) F - q * coeff r F := by
  have e : ∀ m, coeff m (((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 :
      Polynomial ℤ) : PowerSeries ℤ) * F) =
      coeff m F - a * coeff m (X * F) + q * coeff m (X * (X * F)) := by
    intro m
    simp only [Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow, pow_two, sub_mul, add_mul, one_mul,
      mul_assoc, map_sub, map_add, coeff_C_mul]
  refine ⟨?_, fun r => ?_⟩
  · have := congrArg (coeff (0 + 1)) h
    rw [e, coeff_succ_X_mul, coeff_succ_X_mul, coeff_one, if_neg (by omega)] at this
    simp only [coeff_zero_X_mul, mul_zero, add_zero, zero_add] at this
    linarith
  · have := congrArg (coeff (r + 1 + 1)) h
    rw [e, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_one, if_neg (by omega)] at this
    linarith

lemma dichotomy (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ r, coeff (r + 2) (Fv E v) =
        coeff 1 (Fv E v) * coeff (r + 1) (Fv E v) - (P v : ℤ) * coeff r (Fv E v)) ∨
      (∀ r, coeff (r + 2) (Fv E v) = coeff 1 (Fv E v) * coeff (r + 1) (Fv E v)) := by
  have hmul := Fv_mul E v
  have h0 : coeff 0 (Fv E v) = 1 := by simpa using constantCoeff_Fv E v
  simp only [WeierstrassCurve.localPolynomial, card_residue] at hmul
  split_ifs at hmul
  · left
    obtain ⟨h1, hr⟩ := rec_quad _ _ _ hmul
    intro r
    rw [hr r, h1, h0, mul_one]
  all_goals right
  · have hr := rec_linear 1 _ (by simpa using hmul)
    intro r; rw [hr (r + 1), hr 0, h0]; ring
  · have hr := rec_linear (-1) _ (by simpa [sub_eq_add_neg] using hmul)
    intro r; rw [hr (r + 1), hr 0, h0]; ring
  · have hr := rec_linear 0 _ (by simpa using hmul)
    intro r; rw [hr (r + 1), hr 0, h0]; ring

end EulerAux

open EulerAux in
theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) (hp : p.Prime) :
    HorizontalPadicL.LocalEulerFactorDegreeTwo E p ↔
      ¬ HorizontalPadicL.LocalEulerFactorDegreeBelowTwo E p := by
  set v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv).symm ⟨p, hp⟩ with hv
  have hpv : P v = p := by
    rw [hv]
    exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)
  have key : ∀ k, E.LFunction (p ^ k) = coeff k (Fv E v) := fun k => hpv ▸ LFunction_prime_pow E v k
  have k0 : E.LFunction (p ^ 0) = 1 := by rw [key 0]; simpa using constantCoeff_Fv E v
  have k1 : E.LFunction p = coeff 1 (Fv E v) := by simpa using key 1
  unfold HorizontalPadicL.LocalEulerFactorDegreeTwo HorizontalPadicL.LocalEulerFactorDegreeBelowTwo
  simp only [key, k1]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have c0 : coeff 0 (Fv E v) = 1 := by simpa using constantCoeff_Fv E v
  constructor
  · intro h2 h1
    have a := h2 0
    have b := h1 0
    simp only [zero_add, c0, mul_one] at a b
    exact hp0 (by linarith)
  · intro hn
    rcases dichotomy E v with h | h
    · simpa [hpv] using h
    · exact absurd h hn

