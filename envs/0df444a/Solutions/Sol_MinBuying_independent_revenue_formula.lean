-- Prove2me | solution 1 for MinBuying.independent_revenue_formula
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:06:48.672761+00:00
-- url     : https://prove2.me/submissions/979f1a8d-5676-4802-aaa0-3ada6161e161

import Definitions.Def_MinBuying_Model

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace MinBuyingRevenueProof
open MinBuying

private def firstPurchase {n : ℕ} (p : Prices n) (i : Fin n) : Set (Valuations n) :=
  Set.univ.pi (fun j => if j < i then Iio (p j) else if j = i then Ici (p j) else Set.univ)

private lemma firstPurchase_iff {n : ℕ} (p : Prices n) (i : Fin n) (v : Valuations n) :
    v ∈ firstPurchase p i ↔ p i ≤ v i ∧ ∀ j, j < i → v j < p j := by
  simp only [firstPurchase, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h
    constructor
    · simpa using h i
    · intro j hj
      simpa [hj] using h j
  · rintro ⟨hi, hprev⟩ j
    by_cases hj : j < i
    · simpa [hj] using hprev j hj
    · by_cases heq : j = i
      · subst j
        simpa using hi
      · simp [hj, heq]

private lemma firstPurchase_measurable {n : ℕ} (p : Prices n) (i : Fin n) :
    MeasurableSet (firstPurchase p i) := by
  apply MeasurableSet.pi Set.countable_univ
  intro j _
  split_ifs <;> measurability

private lemma payment_sum {n : ℕ} (p : Prices n) (hsorted : Monotone p)
    (v : Valuations n) :
    payment p v = ∑ i : Fin n, (firstPurchase p i).indicator (fun _ => p i) v := by
  classical
  by_cases h : (affordable p v).Nonempty
  · let k := (affordable p v).min' h
    have hk : k ∈ affordable p v := Finset.min'_mem _ _
    have hkval : p k ≤ v k := (Finset.mem_filter.mp hk).2
    have hkle : ∀ j ∈ affordable p v, k ≤ j := by
      intro j hj
      exact Finset.min'_le _ _ hj
    have hpay : payment p v = p k := by
      rw [payment, dif_pos h]
      apply le_antisymm
      · exact Finset.inf'_le _ hk
      · exact Finset.le_inf' h p (fun j hj => hsorted (hkle j hj))
    have hkfirst : v ∈ firstPurchase p k := by
      apply (firstPurchase_iff p k v).mpr
      refine ⟨hkval, ?_⟩
      intro j hj
      by_contra hrej
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hrej⟩
      exact (not_lt_of_ge (hkle j hja)) hj
    have hother : ∀ j, j ≠ k → v ∉ firstPurchase p j := by
      intro j hj hfirst
      obtain ⟨hjval, hprev⟩ := (firstPurchase_iff p j v).mp hfirst
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjval⟩
      have hkj : k < j := lt_of_le_of_ne (hkle j hja) (Ne.symm hj)
      exact (not_lt_of_ge hkval) (hprev k hkj)
    rw [hpay, Finset.sum_eq_single k]
    · simp [hkfirst]
    · intro j _ hj
      exact Set.indicator_of_notMem (hother j hj) _
    · simp
  · have hnone : ∀ i, v ∉ firstPurchase p i := by
      intro i hi
      have hia : i ∈ affordable p v :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((firstPurchase_iff p i v).mp hi).1⟩
      exact h ⟨i, hia⟩
    simp [payment, h, hnone]

private lemma firstPurchase_measure {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (i : Fin n) :
    (Measure.pi F).real (firstPurchase p i) =
      (1 - rejection (F i) (p i)) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), rejection (F j) (p j) := by
  classical
  have htail : (F i).real (Ici (p i)) = 1 - rejection (F i) (p i) := by
    simpa [rejection, Measure.real] using
      (probReal_compl_eq_one_sub (μ := F i) (s := Iio (p i)) measurableSet_Iio)
  simp only [Measure.real, firstPurchase, Measure.pi_pi, ENNReal.toReal_prod]
  have hfactor : ∀ j : Fin n,
      (F j (if j < i then Iio (p j) else if j = i then Ici (p j) else Set.univ)).toReal =
      (if j = i then 1 - rejection (F i) (p i) else 1) *
      (if j < i then rejection (F j) (p j) else 1) := by
    intro j
    by_cases hj : j < i
    · have hne : j ≠ i := ne_of_lt hj
      simp [hj, hne, rejection]
    · by_cases hji : j = i
      · subst j
        simpa [Measure.real] using htail
      · simp [hj, hji]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [Finset.prod_filter]

private lemma differentiated_formula {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (hsorted : Monotone p) :
    Revenue (productLaw F) p = independentRevenueFormula F p := by
  classical
  unfold Revenue independentRevenueFormula productLaw
  simp_rw [payment_sum p hsorted]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (firstPurchase_measurable p i)]
    rw [smul_eq_mul, firstPurchase_measure]
    ring
  · intro i _
    exact (integrable_const (p i)).indicator (firstPurchase_measurable p i)

private lemma uniform_payment {n : ℕ} (q : ℝ) (v : Valuations n) :
    payment (fun _ : Fin n => q) v =
      (Set.univ.pi (fun _ : Fin n => Iio q))ᶜ.indicator (fun _ => q) v := by
  classical
  by_cases h : (affordable (fun _ : Fin n => q) v).Nonempty
  · have hv : v ∉ Set.univ.pi (fun _ : Fin n => Iio q) := by
      obtain ⟨i, hi⟩ := h
      intro hv
      have hlt : v i < q := hv i (Set.mem_univ _)
      have hle : q ≤ v i := (Finset.mem_filter.mp hi).2
      exact not_lt_of_ge hle hlt
    simp [payment, h, hv]
  · have hv : v ∈ Set.univ.pi (fun _ : Fin n => Iio q) := by
      intro i _
      by_contra hi
      apply h
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hi⟩⟩
    simp [payment, h, hv]

private lemma uniform_formula {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (q : ℝ) :
    uniformRevenue (productLaw F) q = q * (1 - ∏ i : Fin n, rejection (F i) q) := by
  have hs : MeasurableSet (Set.univ.pi (fun _ : Fin n => Iio q)) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Iio)
  unfold uniformRevenue Revenue productLaw
  simp_rw [uniform_payment]
  rw [integral_indicator_const _ hs.compl, smul_eq_mul,
    probReal_compl_eq_one_sub hs]
  simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod, rejection]
  ring

end MinBuyingRevenueProof

open MinBuying

theorem solution (n : ℕ) (hn : 0 < n)
    (F : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (p : Prices n) (hp : FeasiblePrices p) (hsorted : Monotone p) :
    Revenue (productLaw F) p = independentRevenueFormula F p ∧
    (∀ q : ℝ, 0 ≤ q →
      uniformRevenue (productLaw F) q = q * (1 - ∏ i : Fin n, rejection (F i) q)) := by
  letI : ∀ i, IsProbabilityMeasure (F i) := fun i => (hF i).1
  exact ⟨MinBuyingRevenueProof.differentiated_formula F p hsorted,
    fun q _ => MinBuyingRevenueProof.uniform_formula F q⟩
