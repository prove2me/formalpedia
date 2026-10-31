-- Prove2me | solution 1 for MinBuying.exchangeable_construction_revenue
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:38:47.282761+00:00
-- url     : https://prove2.me/submissions/d06559f4-35c1-4939-b696-a52a0c745c19

import Definitions.Def_MinBuying_ExchangeableConstruction

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section
namespace MinBuyingGapRevenueProof

private lemma type_size_bounds (n : ℕ) (i : Fin n) : 1 ≤ gapTypeSize n i ∧ gapTypeSize n i ≤ n := by
  refine ⟨le_max_left _ _,max_le (by have hi := i.isLt;omega) (Nat.div_le_self _ _)⟩

private lemma subsets_nonempty (n : ℕ) (i : Fin n) : (gapSubsets n i).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr
  simpa using (type_size_bounds n i).2

private lemma subset_nonempty (n : ℕ) (i : Fin n) (S : Finset (Fin n))
    (hS : S ∈ gapSubsets n i) : S.Nonempty := by
  have hc := (Finset.mem_powersetCard.mp hS).2
  apply Finset.card_pos.mp
  rw [hc]
  exact (type_size_bounds n i).1

private lemma uniformAtoms_integrable {α β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) (g : β → ℝ) :
    Integrable g (uniformAtoms s f) := by
  unfold uniformAtoms
  apply Integrable.smul_measure
  · exact integrable_finsetSum_measure.mpr (fun x _ => integrable_dirac (by simp))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hs.card_pos.ne')

private lemma uniformAtoms_integral {α β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (s : Finset α) (f : α → β) (g : β → ℝ) :
    (∫ v, g v ∂uniformAtoms s f) = (∑ x ∈ s, g (f x))/(s.card : ℝ) := by
  unfold uniformAtoms
  rw [integral_smul_measure,integral_finsetSum_measure (fun x _ => integrable_dirac (by simp))]
  simp [ENNReal.toReal_inv,smul_eq_mul,div_eq_mul_inv,mul_comm]

private lemma weight_nonneg (n : ℕ) (i : Fin n) : 0 ≤ gapTypeWeight n i := by
  unfold gapTypeWeight;positivity

private lemma zero_weight_nonneg (n : ℕ) : 0 ≤ gapZeroWeight n := by
  unfold gapZeroWeight;positivity

private lemma gap_integral (n : ℕ) (f : Valuations n → ℝ) :
    (∫ v, f v ∂exchangeableGapLaw n) =
      gapZeroWeight n * f (fun _ => 0) +
      ∑ i : Fin n, gapTypeWeight n i *
        ((∑ S ∈ gapSubsets n i, f (gapValuation n i S))/((gapSubsets n i).card : ℝ)) := by
  have hi : ∀ i : Fin n, Integrable f (ENNReal.ofReal (gapTypeWeight n i) • gapTypeLaw n i) := by
    intro i
    exact (uniformAtoms_integrable _ (subsets_nonempty n i) _ f).smul_measure ENNReal.ofReal_ne_top
  unfold exchangeableGapLaw
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    (integrable_finsetSum_measure.mpr (fun i _ => hi i))]
  rw [integral_finsetSum_measure (fun i _ => hi i)]
  simp_rw [integral_smul_measure,smul_eq_mul,integral_dirac,
    ENNReal.toReal_ofReal (zero_weight_nonneg n)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal (weight_nonneg n i)]
  congr 1
  exact uniformAtoms_integral _ _ _

private lemma payment_zero_price {n : ℕ} (v : Valuations n) : payment (fun _ => 0) v = 0 := by
  classical
  by_cases h : (affordable (fun _ : Fin n => 0) v).Nonempty <;> simp [payment,h]

private lemma uniform_zero_atom {n : ℕ} (q : ℝ) (hq : 0 < q) :
    payment (fun _ : Fin n => q) (fun _ => 0) = 0 := by
  classical
  have h : ¬ (affordable (fun _ : Fin n => q) (fun _ => 0)).Nonempty := by
    rintro ⟨i,hi⟩
    have := (Finset.mem_filter.mp hi).2
    linarith
  simp [payment,h]

private lemma uniform_atom (n : ℕ) (i : Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (q : ℝ) (hq : 0 < q) :
    payment (fun _ => q) (gapValuation n i S) = if q ≤ 2*(4:ℝ)^i.val then q else 0 := by
  classical
  by_cases hqcap : q ≤ 2*(4:ℝ)^i.val
  · have hn : (affordable (fun _ => q) (gapValuation n i S)).Nonempty := by
      obtain ⟨j,hj⟩ := hS
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [gapValuation,hj] using hqcap⟩⟩
    simp [payment,hn,hqcap]
  · have hn : ¬ (affordable (fun _ => q) (gapValuation n i S)).Nonempty := by
      rintro ⟨j,hj⟩
      have hh := (Finset.mem_filter.mp hj).2
      by_cases hjs : j ∈ S
      · exact hqcap (by simpa [gapValuation,hjs] using hh)
      · have : q ≤ 0 := by simpa [gapValuation,hjs] using hh
        linarith
    simp [payment,hn,hqcap]

private lemma uniform_formula (n : ℕ) (q : ℝ) (hq : 0 < q) :
    uniformRevenue (exchangeableGapLaw n) q =
      ∑ i : Fin n, gapTypeWeight n i * (if q ≤ 2*(4:ℝ)^i.val then q else 0) := by
  unfold uniformRevenue Revenue
  rw [gap_integral,uniform_zero_atom q hq,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hconst : (∑ S ∈ gapSubsets n i, payment (fun _ => q) (gapValuation n i S)) =
      (∑ _S ∈ gapSubsets n i, if q ≤ 2*(4:ℝ)^i.val then q else 0) := by
    apply Finset.sum_congr rfl
    intro S hS
    exact uniform_atom n i S (subset_nonempty n i S hS) q hq
  rw [hconst,Finset.sum_const,nsmul_eq_mul]
  have hc : ((gapSubsets n i).card : ℝ) ≠ 0 := by
    exact_mod_cast (subsets_nonempty n i).card_pos.ne'
  field_simp

private lemma sum_fin_tail (n e : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, if e ≤ i.val then f i.val else 0) = ∑ j ∈ Finset.Ico e n, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if e ≤ j then f j else 0),← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_Ico,and_comm]

private lemma uniform_bound (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    uniformRevenue (exchangeableGapLaw n) q ≤ 1 := by
  classical
  rcases eq_or_lt_of_le hq with rfl | hqpos
  · unfold uniformRevenue Revenue
    simp [payment_zero_price]
  rw [uniform_formula n q hqpos]
  let A : Finset (Fin n) := Finset.univ.filter (fun i => q ≤ 2*(4:ℝ)^i.val)
  by_cases hA : A.Nonempty
  · let e := A.min' hA
    have hemem : e ∈ A := Finset.min'_mem A hA
    have hecap : q ≤ 2*(4:ℝ)^e.val := (Finset.mem_filter.mp hemem).2
    have hele : ∀ i : Fin n, q ≤ 2*(4:ℝ)^i.val → e.val ≤ i.val := by
      intro i hi
      exact Finset.min'_le A i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    have hsum : (∑ i : Fin n, gapTypeWeight n i * (if q ≤ 2*(4:ℝ)^i.val then q else 0)) ≤
        q * ∑ i : Fin n, (if e.val ≤ i.val then gapTypeWeight n i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : q ≤ 2*(4:ℝ)^i.val
      · simp only [hi,if_true,hele i hi]
        exact le_of_eq (mul_comm _ _)
      · simp only [hi,if_false,mul_zero]
        split_ifs
        · exact mul_nonneg hq (weight_nonneg n i)
        · simp
    have htid : (∑ i : Fin n, if e.val ≤ i.val then gapTypeWeight n i else 0) =
        (3/8:ℝ) * ∑ j ∈ Finset.Ico e.val n, (1/4:ℝ)^j := by
      unfold gapTypeWeight
      calc
        (∑ i : Fin n, if e.val ≤ i.val then (3/8:ℝ)*(1/4:ℝ)^i.val else 0)
            = ∑ i : Fin n, (3/8:ℝ)*(if e.val ≤ i.val then (1/4:ℝ)^i.val else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
        _ = (3/8:ℝ)*(∑ i : Fin n, if e.val ≤ i.val then (1/4:ℝ)^i.val else 0) := by rw [Finset.mul_sum]
        _ = _ := by rw [sum_fin_tail]
    rw [htid] at hsum
    have hgeom := geom_sum_Ico_mul_neg (1/4:ℝ) e.isLt.le
    have hgeom' := congrArg (fun x : ℝ => (4:ℝ)^e.val*x) hgeom
    have hcancel : (4:ℝ)^e.val*(1/4:ℝ)^e.val = 1 := by rw [← mul_pow];norm_num
    have hnonneg : 0 ≤ (4:ℝ)^e.val*(1/4:ℝ)^n := by positivity
    have htail : 0 ≤ (3/8:ℝ)*∑ j ∈ Finset.Ico e.val n, (1/4:ℝ)^j := by positivity
    have hup : 2*(4:ℝ)^e.val*((3/8:ℝ)*∑ j ∈ Finset.Ico e.val n, (1/4:ℝ)^j) ≤ 1 := by
      nlinarith only [hgeom',hcancel,hnonneg]
    exact hsum.trans ((mul_le_mul_of_nonneg_right hecap htail).trans hup)
  · have hall : ∀ i : Fin n, ¬ q ≤ 2*(4:ℝ)^i.val := by
      intro i hi
      exact hA ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    simp [hall]

private lemma uniform_positive (n : ℕ) (hn : 0 < n) :
    0 < uniformRevenue (exchangeableGapLaw n) 2 := by
  classical
  rw [uniform_formula n 2 (by norm_num)]
  let i : Fin n := ⟨0,hn⟩
  have hnon : ∀ j : Fin n, 0 ≤ gapTypeWeight n j * (if 2 ≤ 2*(4:ℝ)^j.val then 2 else 0) := by
    intro j
    apply mul_nonneg (weight_nonneg n j)
    split_ifs <;> norm_num
  have hsum := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
  have hzero : gapTypeWeight n i * (if 2 ≤ 2*(4:ℝ)^i.val then 2 else 0) = (3/4:ℝ) := by
    norm_num [gapTypeWeight,i]
  rw [hzero] at hsum
  linarith

private def goodSubsets (n : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  ((Finset.Ioi i).powersetCard (gapTypeSize n i-1)).image (fun T => insert i T)

private lemma upper_not_mem (n : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : T ∈ (Finset.Ioi i).powersetCard (gapTypeSize n i-1)) : i ∉ T := by
  intro hi
  have h := (Finset.mem_powersetCard.mp hT).1 hi
  exact lt_irrefl i (Finset.mem_Ioi.mp h)

private lemma good_subset (n : ℕ) (i : Fin n) : goodSubsets n i ⊆ gapSubsets n i := by
  classical
  intro S hS
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _,?_⟩
  rw [Finset.card_insert_of_notMem (upper_not_mem n i T hT),(Finset.mem_powersetCard.mp hT).2]
  have hk := (type_size_bounds n i).1
  omega

private lemma good_card (n : ℕ) (i : Fin n) :
    (goodSubsets n i).card = (n-1-i.val).choose (gapTypeSize n i-1) := by
  classical
  unfold goodSubsets
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard,Fin.card_Ioi]
  · intro T hT U hU heq
    have ht := upper_not_mem n i T hT
    have hu := upper_not_mem n i U hU
    simpa [ht,hu] using congrArg (fun S : Finset (Fin n) => S.erase i) heq

private lemma payment_nonneg {n : ℕ} (p : Prices n) (hp : FeasiblePrices p) (v : Valuations n) :
    0 ≤ payment p v := by
  classical
  by_cases h : (affordable p v).Nonempty
  · rw [payment,dif_pos h]
    exact Finset.le_inf' h p (fun i _ => hp i)
  · simp [payment,h]

private lemma gapPrices_pos (n : ℕ) (i : Fin n) : 0 < gapPrices n i := by
  unfold gapPrices;positivity

private lemma good_payment (n : ℕ) (i : Fin n) (S : Finset (Fin n)) (hS : S ∈ goodSubsets n i) :
    gapPrices n i ≤ payment (gapPrices n) (gapValuation n i S) := by
  classical
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
  have hi : i ∈ affordable (gapPrices n) (gapValuation n i (insert i T)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [gapPrices,gapValuation,Finset.mem_insert_self,if_true]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) i.val]
  have hnon := (show (affordable (gapPrices n) (gapValuation n i (insert i T))).Nonempty from ⟨i,hi⟩)
  rw [payment,dif_pos hnon]
  apply Finset.le_inf'
  intro j hj
  have hja := (Finset.mem_filter.mp hj).2
  have hjs : j ∈ insert i T := by
    by_contra h
    have hle : gapPrices n j ≤ 0 := by simpa [gapValuation,h] using hja
    exact not_le_of_gt (gapPrices_pos n j) hle
  have hij : i ≤ j := by
    rcases Finset.mem_insert.mp hjs with h | h
    · simpa [h]
    · exact (Finset.mem_Ioi.mp ((Finset.mem_powersetCard.mp hT).1 h)).le
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hij

private lemma type_revenue_lower (n : ℕ) (i : Fin n) :
    gapPrices n i * ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
        (n.choose (gapTypeSize n i) : ℝ) ≤
      (∑ S ∈ gapSubsets n i, payment (gapPrices n) (gapValuation n i S)) /
        ((gapSubsets n i).card : ℝ) := by
  classical
  have hs1 : (goodSubsets n i).card * gapPrices n i ≤
      ∑ S ∈ goodSubsets n i, payment (gapPrices n) (gapValuation n i S) := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    exact Finset.sum_le_sum (fun S hS => good_payment n i S hS)
  have hs2 : (∑ S ∈ goodSubsets n i, payment (gapPrices n) (gapValuation n i S)) ≤
      ∑ S ∈ gapSubsets n i, payment (gapPrices n) (gapValuation n i S) :=
    Finset.sum_le_sum_of_subset_of_nonneg (good_subset n i)
      (fun S _ _ => payment_nonneg _ (fun j => (gapPrices_pos n j).le) _)
  have hc : (gapSubsets n i).card = n.choose (gapTypeSize n i) := by
    simp [gapSubsets,Finset.card_powersetCard]
  rw [hc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [good_card] at hs1
  simpa only [mul_comm] using hs1.trans hs2

private lemma weight_price (n : ℕ) (i : Fin n) : gapTypeWeight n i * gapPrices n i = (3/8:ℝ) := by
  unfold gapTypeWeight gapPrices
  rw [mul_assoc,← mul_pow]
  norm_num

private lemma differentiated_lower (n : ℕ) :
    (3/8:ℝ) * (∑ i : Fin n, ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
        (n.choose (gapTypeSize n i) : ℝ)) ≤ Revenue (exchangeableGapLaw n) (gapPrices n) := by
  classical
  unfold Revenue
  rw [gap_integral,Finset.mul_sum]
  have hz : 0 ≤ gapZeroWeight n * payment (gapPrices n) (fun _ => 0) :=
    mul_nonneg (zero_weight_nonneg n) (payment_nonneg _ (fun i => (gapPrices_pos n i).le) _)
  apply le_trans _ (le_add_of_nonneg_left hz)
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (type_revenue_lower n i) (weight_nonneg n i)
  simpa only [← mul_div_assoc,← mul_assoc,weight_price] using h

end MinBuyingGapRevenueProof

theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ q : ℝ, 0 ≤ q → uniformRevenue (exchangeableGapLaw n) q ≤ 1) ∧
    0 < uniformRevenue (exchangeableGapLaw n) 2 ∧
    (3/8:ℝ) * (∑ i : Fin n, ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
      (n.choose (gapTypeSize n i) : ℝ)) ≤ Revenue (exchangeableGapLaw n) (gapPrices n) := by
  exact ⟨MinBuyingGapRevenueProof.uniform_bound n,MinBuyingGapRevenueProof.uniform_positive n hn,
    MinBuyingGapRevenueProof.differentiated_lower n⟩
