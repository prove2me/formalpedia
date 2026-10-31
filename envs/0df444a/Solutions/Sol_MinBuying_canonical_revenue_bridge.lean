-- Prove2me | solution 1 for MinBuying.canonical_revenue_bridge
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:30:01.928233+00:00
-- url     : https://prove2.me/submissions/bcab99ca-08ba-4b31-933d-17cc98bdc623

import Theorems.Thm_MinBuying_triangular_law_specification
import Theorems.Thm_MinBuying_independent_revenue_formula
import Theorems.Thm_MinBuying_triangular_wellposed

open MeasureTheory Set MinBuying
open scoped BigOperators

noncomputable section

private def lastPurchase {n : ℕ} (p : Prices n) (i : Fin n) : Set (Valuations n) :=
  Set.univ.pi (fun j => if i < j then Iio (p j) else if j = i then Ici (p j) else Set.univ)

private lemma lastPurchase_iff {n : ℕ} (p : Prices n) (i : Fin n) (v : Valuations n) :
    v ∈ lastPurchase p i ↔ p i ≤ v i ∧ ∀ j, i < j → v j < p j := by
  simp only [lastPurchase, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h
    constructor
    · simpa using h i
    · intro j hj
      simpa [hj] using h j
  · rintro ⟨hi, hprev⟩ j
    by_cases hj : i < j
    · simpa [hj] using hprev j hj
    · by_cases heq : j = i
      · subst j
        simpa using hi
      · simp [hj, heq]

private lemma lastPurchase_measurable {n : ℕ} (p : Prices n) (i : Fin n) :
    MeasurableSet (lastPurchase p i) := by
  apply MeasurableSet.pi Set.countable_univ
  intro j _
  split_ifs <;> measurability

private lemma payment_sum {n : ℕ} (p : Prices n) (hsorted : Antitone p)
    (v : Valuations n) :
    payment p v = ∑ i : Fin n, (lastPurchase p i).indicator (fun _ => p i) v := by
  classical
  by_cases h : (affordable p v).Nonempty
  · let k := (affordable p v).max' h
    have hk : k ∈ affordable p v := Finset.max'_mem _ _
    have hkval : p k ≤ v k := (Finset.mem_filter.mp hk).2
    have hkle : ∀ j ∈ affordable p v, j ≤ k := by
      intro j hj
      exact Finset.le_max' _ _ hj
    have hpay : payment p v = p k := by
      rw [payment, dif_pos h]
      apply le_antisymm
      · exact Finset.inf'_le _ hk
      · exact Finset.le_inf' h p (fun j hj => hsorted (hkle j hj))
    have hkfirst : v ∈ lastPurchase p k := by
      apply (lastPurchase_iff p k v).mpr
      refine ⟨hkval, ?_⟩
      intro j hj
      by_contra hrej
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hrej⟩
      exact (not_lt_of_ge (hkle j hja)) hj
    have hother : ∀ j, j ≠ k → v ∉ lastPurchase p j := by
      intro j hj hfirst
      obtain ⟨hjval, hprev⟩ := (lastPurchase_iff p j v).mp hfirst
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjval⟩
      have hkj : j < k := lt_of_le_of_ne (hkle j hja) hj
      exact (not_lt_of_ge hkval) (hprev k hkj)
    rw [hpay, Finset.sum_eq_single k]
    · simp [hkfirst]
    · intro j _ hj
      exact Set.indicator_of_notMem (hother j hj) _
    · simp
  · have hnone : ∀ i, v ∉ lastPurchase p i := by
      intro i hi
      have hia : i ∈ affordable p v :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((lastPurchase_iff p i v).mp hi).1⟩
      exact h ⟨i, hia⟩
    simp [payment, h, hnone]

private lemma lastPurchase_measure {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (i : Fin n) :
    (Measure.pi F).real (lastPurchase p i) =
      (1 - rejection (F i) (p i)) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), rejection (F j) (p j) := by
  classical
  have htail : (F i).real (Ici (p i)) = 1 - rejection (F i) (p i) := by
    simpa [rejection, Measure.real] using
      (probReal_compl_eq_one_sub (μ := F i) (s := Iio (p i)) measurableSet_Iio)
  simp only [Measure.real, lastPurchase, Measure.pi_pi, ENNReal.toReal_prod]
  have hfactor : ∀ j : Fin n,
      (F j (if i < j then Iio (p j) else if j = i then Ici (p j) else Set.univ)).toReal =
      (if j = i then 1 - rejection (F i) (p i) else 1) *
      (if i < j then rejection (F j) (p j) else 1) := by
    intro j
    by_cases hj : i < j
    · have hne : j ≠ i := ne_of_gt hj
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
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (hsorted : Antitone p) :
    Revenue (productLaw F) p =
      ∑ i : Fin n, p i * (1 - rejection (F i) (p i)) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), rejection (F j) (p j) := by
  classical
  unfold Revenue productLaw
  simp_rw [payment_sum p hsorted]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (lastPurchase_measurable p i)]
    rw [smul_eq_mul, lastPurchase_measure]
    ring
  · intro i _
    exact (integrable_const (p i)).indicator (lastPurchase_measurable p i)


private lemma affine_fold (n : ℕ) (b r : Fin n → ℝ) (C : ℝ) :
    (List.finRange n).foldl (fun X i => b i + r i * X) C =
      C * ∏ i, r i + ∑ i : Fin n, b i * ∏ j ∈ Finset.univ.filter (fun j => i < j), r j := by
  induction n generalizing C with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map, ih]
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hzero : (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => 0 < j), r j) =
        ∏ j : Fin n, r j.succ := by
      rw [Finset.prod_filter, Fin.prod_univ_succ]
      simp
    have hsucc (i : Fin n) :
        (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i.succ < j), r j) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), r j.succ := by
      rw [Finset.prod_filter, Fin.prod_univ_succ, Finset.prod_filter]
      simp
    rw [hzero]
    simp_rw [hsucc]
    ring

private lemma canonical_antitone (I : CanonicalInstance) : Antitone (canonicalPrices I) := by
  have h : StrictAnti (canonicalPrices I) :=
    (Fin.strictMono_cons (α := ℝᵒᵈ)).mpr ⟨I.cap_lt_terminal, I.caps_decreasing⟩
  exact h.antitone

private lemma tri_valid {n : ℕ} (I : TriangularInstance n) (i : Fin n) :
    ValidMarginal (triangularMarginals I i) :=
  (triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).1

private lemma tri_uniform {n : ℕ} (hn : 0 < n) (I : TriangularInstance n) (p : ℝ) (hp : 0 ≤ p) :
    uniformRevenue (triangularJoint I) p = p * (1 - ∏ i, triangularReject (I.a i) (I.cap i) p) := by
  have h := (independent_revenue_formula n hn (triangularMarginals I) (tri_valid I)
    (fun _ => 0) (fun _ => le_rfl) (fun _ _ _ => le_rfl)).2 p hp
  change uniformRevenue (triangularJoint I) p = _ at h
  rw [h]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  exact (triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).2.2.1 p

private lemma tri_cap_revenue {n : ℕ} (I : TriangularInstance n) (hI : Antitone I.cap) :
    Revenue (triangularJoint I) I.cap =
      (List.finRange n).foldl (fun C i => continuationStep (I.a i) (I.cap i) C) 0 := by
  haveI : ∀ i, IsProbabilityMeasure (triangularMarginals I i) := fun i => (tri_valid I i).1
  have hrejection (i : Fin n) : rejection (triangularMarginals I i) (I.cap i) =
      I.cap i / (I.cap i + I.a i) := by
    change rejection (triangularLaw (I.a i) (I.cap i)) (I.cap i) = _
    rw [(triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).2.2.1]
    simp [triangularReject, not_le_of_gt (I.cap_pos i)]
  have hform := differentiated_formula (triangularMarginals I) I.cap hI
  change Revenue (triangularJoint I) I.cap = _ at hform
  rw [hform]
  simp_rw [hrejection]
  have hf := affine_fold n (fun i => I.cap i * (1 - I.cap i / (I.cap i + I.a i)))
    (fun i => I.cap i / (I.cap i + I.a i)) 0
  simp only [zero_mul, zero_add] at hf
  rw [← hf]
  congr 1
  funext C i
  unfold continuationStep
  have hv := I.cap_pos i
  have ha := I.a_pos i
  have hden : 0 < 1 + I.a i / I.cap i := by positivity
  field_simp [hv.ne', (add_pos hv ha).ne', hden.ne']
  ring

private lemma canonical_cap_revenue (I : CanonicalInstance) :
    Revenue (canonicalLaw I) (canonicalPrices I) = canonicalCapRevenue I := by
  have h := tri_cap_revenue (canonicalParameters I) (canonical_antitone I)
  change Revenue (canonicalLaw I) (canonicalPrices I) = _ at h
  rw [h]
  rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
  simp only [canonicalParameters, Fin.cons_zero, Fin.cons_succ]
  have hinit : continuationStep 1 I.terminalCap 0 = I.terminalCap / (I.terminalCap + 1) := by
    unfold continuationStep
    have hp : 0 < I.terminalCap := lt_trans zero_lt_one I.terminal_one_lt
    field_simp
    ring
  rw [hinit]
  simp [canonicalCapRevenue, canonicalContinuation, List.take_of_length_le]

theorem solution (I : CanonicalInstance) :
    ValidLaw (canonicalLaw I) ∧
    WellPosed (canonicalLaw I) ∧
    Revenue (canonicalLaw I) (canonicalPrices I) = canonicalCapRevenue I ∧
    (∀ p : ℝ, 0 ≤ p →
      uniformRevenue (canonicalLaw I) p = canonicalUniformRevenueAt I p) := by
  have hw := triangular_wellposed (I.count + 1) (by omega) (canonicalParameters I)
  refine ⟨hw.1, hw.2, canonical_cap_revenue I, ?_⟩
  intro p hp
  have h := tri_uniform (by omega) (canonicalParameters I) p hp
  simpa [canonicalLaw, canonicalUniformRevenueAt, canonicalParameters,
    Fin.prod_univ_succ] using h
