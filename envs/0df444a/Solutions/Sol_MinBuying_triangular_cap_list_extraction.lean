-- Prove2me | solution 1 for MinBuying.triangular_cap_list_extraction
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:51:58.871187+00:00
-- url     : https://prove2.me/submissions/77da7a1c-9428-4c52-972e-f18d312977f6

import Theorems.Thm_MinBuying_triangular_price_raising
import Theorems.Thm_MinBuying_triangular_wellposed
import Theorems.Thm_MinBuying_triangular_law_specification
import Theorems.Thm_MinBuying_independent_revenue_formula

open MeasureTheory Set Filter MinBuying
open scoped BigOperators Topology
noncomputable section

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


private lemma payment_permute {n : ℕ} (p : Prices n)
    (σ : Equiv.Perm (Fin n)) (v : Valuations n) :
    payment (p ∘ σ) v = payment p (v ∘ σ.symm) := by
  classical
  have himage : (affordable (p ∘ σ) v).image σ = affordable p (v ∘ σ.symm) := by
    ext i
    simp only [Finset.mem_image, affordable, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.comp_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, σ.apply_symm_apply i⟩
  by_cases h : (affordable (p ∘ σ) v).Nonempty
  · have hr : (affordable p (v ∘ σ.symm)).Nonempty := by
      rw [← himage]
      exact h.image σ
    rw [payment, dif_pos h, payment, dif_pos hr]
    rw [Finset.inf'_comp_eq_image h p]
    simp only [himage]
  · have hr : ¬ (affordable p (v ∘ σ.symm)).Nonempty := by
      rw [← himage, Finset.image_nonempty]
      exact h
    simp only [payment, dif_neg h, dif_neg hr]

private lemma revenue_permute {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (σ : Equiv.Perm (Fin n)) :
    Revenue (productLaw (F ∘ σ)) (p ∘ σ) = Revenue (productLaw F) p := by
  unfold Revenue productLaw
  simp_rw [payment_permute]
  have hmp := measurePreserving_piCongrLeft F σ
  convert hmp.integral_comp' (payment p) using 1
  congr 1
  funext v
  congr 1
  funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

private lemma fold_filter {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (f : ℝ → α → ℝ) (C : ℝ) :
    (l.filter (fun x => P x)).foldl f C =
      l.foldl (fun S x => if P x then f S x else S) C := by
  induction l generalizing C with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : P x <;> simp [hx,ih]

private lemma filtered_product_ge {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    (l.map f).prod ≤ ((l.filter (fun x => P x)).map f).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : P x
    · simpa [hx] using mul_le_mul_of_nonneg_left ih (h0 x)
    · simp only [List.filter_cons,decide_eq_false hx,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.prod_cons]
      have hprod : 0 ≤ (l.map f).prod := List.prod_nonneg (by
        intro y hy
        obtain ⟨z,_,rfl⟩ := List.mem_map.mp hy
        exact h0 z)
      exact (mul_le_of_le_one_left hprod (h1 x)).trans ih

theorem solution (n : ℕ) (hn : 0 < n) (I : TriangularInstance n)
    (hNorm : UPRevenue (triangularJoint I) = 1) :
    ∃ L : List (ℝ × ℝ), L.length ≤ n ∧
      (∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) ∧
      L.Pairwise (fun x y => y.2 ≤ x.2) ∧
      DPRevenue (triangularJoint I) ≤ L.foldl (fun C x => continuationStep x.1 x.2 C) 0 ∧
      (∀ t : ℝ, 0 < t → t * (1 - (L.map (fun x => triangularReject x.1 x.2 t)).prod) ≤ 1) := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (triangularMarginals I i) := (tri_valid I i).1
  have hW := (triangular_wellposed n hn I).2
  let M := 1 + ∑ i, I.cap i
  have hM : 0 < M := by
    have hs : 0 ≤ ∑ i, I.cap i := Finset.sum_nonneg (fun i _ => (I.cap_pos i).le)
    dsimp [M]
    linarith
  have hcapM (i : Fin n) : I.cap i < M := by
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => (I.cap_pos j).le) (Finset.mem_univ i)
    dsimp [M]
    linarith
  obtain ⟨p,hp,hpopt⟩ := hW.2.2.1
  obtain ⟨A,hA⟩ := finite_policy_domination I M hM hcapM p hp
  let q : Prices n := fun i => if i ∈ A then I.cap i else M
  let σ := Tuple.sort (fun i => OrderDual.toDual (q i))
  letI (i : Fin n) : IsProbabilityMeasure ((triangularMarginals I ∘ σ) i) :=
    (tri_valid I (σ i)).1
  have hsort : Antitone (q ∘ σ) := Tuple.monotone_sort (fun i => OrderDual.toDual (q i))
  let ids := (List.finRange n).filter (fun i => σ i ∈ A)
  let L : List (ℝ × ℝ) := ids.map (fun i => (I.a (σ i),I.cap (σ i)))
  have hlen : L.length ≤ n := by
    simpa [L,ids] using List.length_filter_le (fun i : Fin n => decide (σ i ∈ A)) (List.finRange n)
  have hpar : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨I.a_pos (σ i),I.cap_pos (σ i)⟩
  have hdec : L.Pairwise (fun x y => y.2 ≤ x.2) := by
    rw [List.pairwise_map,List.pairwise_filter]
    apply (List.pairwise_lt_finRange n).imp
    intro i j hij hi hj
    have h := hsort hij.le
    simpa [Function.comp_apply,q,of_decide_eq_true hi,of_decide_eq_true hj] using h
  have hr (i : Fin n) : rejection (triangularMarginals I (σ i)) (q (σ i)) =
      if σ i ∈ A then I.cap (σ i) / (I.cap (σ i)+I.a (σ i)) else 1 := by
    change rejection (triangularLaw (I.a (σ i)) (I.cap (σ i))) (q (σ i)) = _
    rw [(triangular_law_specification _ _ (I.a_pos (σ i)) (I.cap_pos (σ i))).2.2.1]
    by_cases hi : σ i ∈ A
    · simp [q,hi,triangularReject,not_le_of_gt (I.cap_pos (σ i))]
    · simp [q,hi,triangularReject,not_le_of_gt hM,not_le_of_gt (hcapM (σ i))]
  have hstep (C : ℝ) (i : Fin n) :
      q (σ i) * (1 - rejection (triangularMarginals I (σ i)) (q (σ i))) +
        rejection (triangularMarginals I (σ i)) (q (σ i)) * C =
      if σ i ∈ A then continuationStep (I.a (σ i)) (I.cap (σ i)) C else C := by
    rw [hr]
    by_cases hi : σ i ∈ A
    · simp only [hi,if_pos,q,continuationStep]
      have hv := ne_of_gt (I.cap_pos (σ i))
      have ha := ne_of_gt (add_pos (I.cap_pos (σ i)) (I.a_pos (σ i)))
      field_simp
      <;> ring
    · simp [hi]
  have hrev : Revenue (triangularJoint I) q = L.foldl (fun C x => continuationStep x.1 x.2 C) 0 := by
    rw [triangularJoint,← revenue_permute (triangularMarginals I) q σ]
    rw [differentiated_formula _ _ hsort]
    simp only [Function.comp_apply]
    have hf := affine_fold n
      (fun i => q (σ i) * (1-rejection (triangularMarginals I (σ i)) (q (σ i))))
      (fun i => rejection (triangularMarginals I (σ i)) (q (σ i))) 0
    simp only [zero_mul,zero_add] at hf
    rw [← hf]
    simp_rw [hstep]
    dsimp only [L]
    rw [List.foldl_map]
    exact (fold_filter (List.finRange n) (fun i => σ i ∈ A)
      (fun C i => continuationStep (I.a (σ i)) (I.cap (σ i)) C) 0).symm
  refine ⟨L,hlen,hpar,hdec,?_,?_⟩
  · rw [← hrev,← hpopt]
    exact hA
  · intro t ht
    have h0 (i : Fin n) : 0 ≤ triangularReject (I.a (σ i)) (I.cap (σ i)) t := by
      rw [← (triangular_law_specification _ _ (I.a_pos (σ i)) (I.cap_pos (σ i))).2.2.1]
      exact ENNReal.toReal_nonneg
    have h1 (i : Fin n) : triangularReject (I.a (σ i)) (I.cap (σ i)) t ≤ 1 := by
      letI : IsProbabilityMeasure (triangularLaw (I.a (σ i)) (I.cap (σ i))) :=
        (triangular_law_specification _ _ (I.a_pos (σ i)) (I.cap_pos (σ i))).1.1
      rw [← (triangular_law_specification _ _ (I.a_pos (σ i)) (I.cap_pos (σ i))).2.2.1]
      exact measureReal_le_one
    have hprod : ∏ i, triangularReject (I.a i) (I.cap i) t ≤
        (L.map (fun x => triangularReject x.1 x.2 t)).prod := by
      rw [← Equiv.prod_comp σ (fun i => triangularReject (I.a i) (I.cap i) t), Fin.prod_univ_def]
      simpa [L,ids,List.map_map,Function.comp_def] using
        filtered_product_ge (List.finRange n) (fun i => σ i ∈ A)
          (fun i => triangularReject (I.a (σ i)) (I.cap (σ i)) t) h0 h1
    have hu : uniformRevenue (triangularJoint I) t ≤ 1 := by
      rw [← hNorm]
      exact le_csSup hW.2.1 ⟨t,ht.le,rfl⟩
    rw [tri_uniform hn I t ht.le] at hu
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hprod 1) ht.le).trans hu


