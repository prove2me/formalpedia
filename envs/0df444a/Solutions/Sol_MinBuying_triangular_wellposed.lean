-- Prove2me | solution 1 for MinBuying.triangular_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:29:54.639145+00:00
-- url     : https://prove2.me/submissions/b718659e-3275-43e9-8549-e83ee5bba855

import Theorems.Thm_MinBuying_triangular_law_specification
import Theorems.Thm_MinBuying_independent_revenue_formula
import Theorems.Thm_MinBuying_triangular_price_raising

open MeasureTheory Set MinBuying
open scoped BigOperators

private lemma tri_valid {n : ℕ} (I : TriangularInstance n) (i : Fin n) :
    ValidMarginal (triangularMarginals I i) :=
  (triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).1

private lemma tri_support {n : ℕ} (I : TriangularInstance n) :
    ∀ᵐ v ∂triangularJoint I, ∀ i, v i ∈ Icc (0 : ℝ) (I.cap i) := by
  haveI : ∀ i, IsProbabilityMeasure (triangularMarginals I i) := fun i => (tri_valid I i).1
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae
    (triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).2.2.2.2.2

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

private lemma payment_agrees {n : ℕ} (p q : Prices n) (v : Valuations n)
    (ha : ∀ i, p i ≤ v i ↔ q i ≤ v i)
    (hv : ∀ i, p i ≤ v i → p i = q i) : payment p v = payment q v := by
  have hA : affordable p v = affordable q v := by
    ext i
    simp [affordable, ha]
  unfold payment
  rw [hA]
  split_ifs with h
  · apply Finset.inf'_congr h rfl
    intro i hi
    exact hv i ((ha i).mpr (Finset.mem_filter.mp hi).2)
  · rfl

private lemma payment_nonnegative {n : ℕ} (p : Prices n) (hp : FeasiblePrices p)
    (v : Valuations n) : 0 ≤ payment p v := by
  unfold payment
  split_ifs with h
  · exact Finset.le_inf' h p (fun i _ => hp i)
  · rfl

private lemma empty_payment {n : ℕ} (p : Prices n) (v : Valuations n)
    (hv : ∀ i, v i < p i) : payment p v = 0 := by
  have hnone : ¬ (affordable p v).Nonempty := by
    rintro ⟨i, hi⟩
    exact (not_le_of_gt (hv i)) (Finset.mem_filter.mp hi).2
  simp [payment, hnone]

private lemma cap_policy_feasible {n : ℕ} (I : TriangularInstance n) (M : ℝ) (hM : 0 ≤ M)
    (A : Finset (Fin n)) : FeasiblePrices (fun i => if i ∈ A then I.cap i else M) := by
  intro i
  change 0 ≤ if i ∈ A then I.cap i else M
  split_ifs
  · exact (I.cap_pos i).le
  · exact hM

private lemma finite_policy_domination {n : ℕ} (I : TriangularInstance n) (M : ℝ)
    (hM : 0 < M) (hcapM : ∀ i, I.cap i < M) (p : Prices n) (hp : FeasiblePrices p) :
    ∃ A : Finset (Fin n), Revenue (triangularJoint I) p ≤
      Revenue (triangularJoint I) (fun i => if i ∈ A then I.cap i else M) := by
  classical
  let A := Finset.univ.filter (fun i => p i ≤ I.cap i)
  let q : Prices n := fun i => if p i ≤ I.cap i then I.cap i else max M (p i)
  have hq : FeasiblePrices q := by
    intro i
    dsimp [q]
    split_ifs
    · exact (I.cap_pos i).le
    · exact hM.le.trans (le_max_left _ _)
  have hpq : ∀ i, p i ≤ q i := by
    intro i
    dsimp [q]
    split_ifs with hi
    · exact hi
    · exact le_max_right _ _
  have hact : ∀ i, p i ≤ I.cap i → q i ≤ I.cap i := by
    intro i hi
    simp [q, hi]
  have hraise := triangular_price_raising n I p q hp hq hpq hact
  refine ⟨A, hraise.trans_eq ?_⟩
  apply integral_congr_ae
  filter_upwards [tri_support I] with v hv
  apply payment_agrees
  · intro i
    by_cases hi : p i ≤ I.cap i
    · simp [q, A, hi]
    · have hvM : v i < M := lt_of_le_of_lt (hv i).2 (hcapM i)
      have hvmax : v i < max M (p i) := hvM.trans_le (le_max_left _ _)
      simp [q, A, hi, not_le_of_gt hvM, not_le_of_gt hvmax]
  · intro i hqi
    by_cases hi : p i ≤ I.cap i
    · simp [q, A, hi]
    · have hvM : v i < M := lt_of_le_of_lt (hv i).2 (hcapM i)
      have hvmax : v i < max M (p i) := hvM.trans_le (le_max_left _ _)
      exact False.elim ((not_le_of_gt hvmax) (by simpa [q, hi] using hqi))

private lemma uniform_cap_domination {n : ℕ} (hn : 0 < n) (I : TriangularInstance n)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ i : Fin n, uniformRevenue (triangularJoint I) p ≤ uniformRevenue (triangularJoint I) (I.cap i) := by
  classical
  let A := Finset.univ.filter (fun i => p ≤ I.cap i)
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi, hmin⟩ := A.exists_min_image I.cap hA
    have hpi : p ≤ I.cap i := (Finset.mem_filter.mp hi).2
    refine ⟨i, ?_⟩
    exact triangular_price_raising n I (fun _ => p) (fun _ => I.cap i)
      (fun _ => hp) (fun _ => (I.cap_pos i).le) (fun _ => hpi)
      (fun j hj => hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  · let i : Fin n := ⟨0, hn⟩
    refine ⟨i, ?_⟩
    have hzero : uniformRevenue (triangularJoint I) p = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [tri_support I] with v hv
      apply empty_payment
      intro j
      have hj : I.cap j < p := by
        by_contra h
        exact hA ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩⟩
      exact lt_of_le_of_lt (hv j).2 hj
    rw [hzero]
    exact integral_nonneg (fun v => payment_nonnegative (fun _ => I.cap i) (fun _ => (I.cap_pos i).le) v)

private lemma positive_uniform {n : ℕ} (hn : 0 < n) (I : TriangularInstance n) :
    ∃ p : ℝ, 0 ≤ p ∧ 0 < uniformRevenue (triangularJoint I) p := by
  let i : Fin n := ⟨0, hn⟩
  let p := I.cap i
  have hp : 0 < p := I.cap_pos i
  refine ⟨p, hp.le, ?_⟩
  rw [tri_uniform hn I p hp.le]
  apply mul_pos hp
  apply sub_pos.mpr
  have hpos : ∀ j : Fin n, 0 < triangularReject (I.a j) (I.cap j) p := by
    intro j
    simp only [triangularReject, if_neg (not_le_of_gt hp)]
    split_ifs
    · exact div_pos hp (add_pos hp (I.a_pos j))
    · norm_num
  have hle : ∀ j : Fin n, triangularReject (I.a j) (I.cap j) p ≤ 1 := by
    intro j
    simp only [triangularReject, if_neg (not_le_of_gt hp)]
    split_ifs
    · exact (div_le_one (add_pos hp (I.a_pos j))).mpr (le_add_of_nonneg_right (I.a_pos j).le)
    · rfl
  have hi : triangularReject (I.a i) (I.cap i) p < 1 := by
    simp only [triangularReject, if_neg (not_le_of_gt hp), show p ≤ I.cap i from le_rfl, if_true]
    exact (div_lt_one (add_pos hp (I.a_pos i))).mpr (lt_add_of_pos_right _ (I.a_pos i))
  simpa using Finset.prod_lt_prod (s := Finset.univ) (fun j _ => hpos j)
    (fun j _ => hle j) ⟨i, Finset.mem_univ _, hi⟩

theorem solution (n : ℕ) (hn : 0 < n) (I : TriangularInstance n) :
    ValidLaw (triangularJoint I) ∧ WellPosed (triangularJoint I) := by
  classical
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  haveI : ∀ i, IsProbabilityMeasure (triangularMarginals I i) := fun i => (tri_valid I i).1
  have hvalid : ValidLaw (triangularJoint I) := by
    constructor
    · dsimp [triangularJoint, productLaw]
      infer_instance
    · filter_upwards [tri_support I] with v hv
      exact fun i => (hv i).1
  let M := 1 + ∑ i, I.cap i
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ i, I.cap i := Finset.sum_nonneg (fun i _ => (I.cap_pos i).le)
    dsimp [M]
    linarith
  have hcapM : ∀ i, I.cap i < M := by
    intro i
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => (I.cap_pos j).le) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let policy := fun A : Finset (Fin n) => fun i => if i ∈ A then I.cap i else M
  obtain ⟨A, _, hA⟩ := Finset.univ.exists_max_image
    (fun A : Finset (Fin n) => Revenue (triangularJoint I) (policy A)) Finset.univ_nonempty
  have hAD : ∀ r ∈ differentiatedValues (triangularJoint I), r ≤ Revenue (triangularJoint I) (policy A) := by
    rintro r ⟨p, hp, rfl⟩
    obtain ⟨B, hB⟩ := finite_policy_domination I M hM hcapM p hp
    exact hB.trans (hA B (Finset.mem_univ _))
  have hAp : FeasiblePrices (policy A) := cap_policy_feasible I M hM.le A
  have hAd : Revenue (triangularJoint I) (policy A) ∈ differentiatedValues (triangularJoint I) :=
    ⟨policy A, hAp, rfl⟩
  have hDbdd : BddAbove (differentiatedValues (triangularJoint I)) := ⟨_, hAD⟩
  have hDopt : Revenue (triangularJoint I) (policy A) = DPRevenue (triangularJoint I) :=
    le_antisymm (le_csSup hDbdd hAd) (csSup_le ⟨_, hAd⟩ hAD)
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
    (fun i : Fin n => uniformRevenue (triangularJoint I) (I.cap i)) Finset.univ_nonempty
  have hIU : ∀ r ∈ uniformValues (triangularJoint I), r ≤ uniformRevenue (triangularJoint I) (I.cap i) := by
    rintro r ⟨p, hp, rfl⟩
    obtain ⟨j, hj⟩ := uniform_cap_domination hn I p hp
    exact hj.trans (hi j (Finset.mem_univ _))
  have hIu : uniformRevenue (triangularJoint I) (I.cap i) ∈ uniformValues (triangularJoint I) :=
    ⟨I.cap i, (I.cap_pos i).le, rfl⟩
  have hUbdd : BddAbove (uniformValues (triangularJoint I)) := ⟨_, hIU⟩
  have hUopt : uniformRevenue (triangularJoint I) (I.cap i) = UPRevenue (triangularJoint I) :=
    le_antisymm (le_csSup hUbdd hIu) (csSup_le ⟨_, hIu⟩ hIU)
  refine ⟨hvalid, hDbdd, hUbdd, ⟨policy A, hAp, hDopt⟩,
    ⟨I.cap i, (I.cap_pos i).le, hUopt⟩, ?_⟩
  obtain ⟨p, hp, hpR⟩ := positive_uniform hn I
  exact hpR.trans_le (le_csSup hUbdd ⟨p, hp, rfl⟩)
