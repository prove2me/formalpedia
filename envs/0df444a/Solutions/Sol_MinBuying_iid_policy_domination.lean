-- Prove2me | solution 1 for MinBuying.iid_policy_domination
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:08:34.538+00:00
-- url     : https://prove2.me/submissions/d942b857-e2fa-44fd-bacc-806d5f6d9c16

import Theorems.Thm_MinBuying_independent_revenue_formula

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

namespace MinBuyingIIDProof

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

private lemma iid_revenue_permute {n : ℕ} (F : Measure ℝ)
    [IsProbabilityMeasure F] (p : Prices n) (σ : Equiv.Perm (Fin n)) :
    Revenue (iidLaw n F) (p ∘ σ) = Revenue (iidLaw n F) p := by
  unfold Revenue iidLaw productLaw
  simp_rw [payment_permute]
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => F) σ
  convert hmp.integral_comp' (payment p) using 1
  congr 1
  funext v
  congr 1
  funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

private def G (n : ℕ) (r : ℝ) : ℝ := ∑ j ∈ Finset.range n, r ^ j

private lemma G_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ G n r := by
  exact Finset.sum_nonneg (fun j _ => pow_nonneg hr j)

private lemma G_pos (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 < G (n+1) r :=
  geom_sum_pos hr (Nat.succ_ne_zero n)

private lemma G_succ (n : ℕ) (r : ℝ) : G (n+1) r = r * G n r + 1 :=
  geom_sum_succ

private lemma G_succ' (n : ℕ) (r : ℝ) : G (n+1) r = r^n + G n r :=
  geom_sum_succ'

private lemma G_mul (n : ℕ) (r : ℝ) : G n r * (1-r) = 1-r^n :=
  geom_sum_mul_neg r n

private lemma G_ratio {r s : ℝ} (n : ℕ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    G n s * G (n+1) r ≤ G n r * G (n+1) s := by
  have hs : 0 ≤ s := hr.trans hrs
  have hcross : r^n * G n s ≤ s^n * G n r := by
    simp only [G, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt (Finset.mem_range.mp hj)
    have hpow : r^(n-j) ≤ s^(n-j) := pow_le_pow_left₀ hr hrs (n-j)
    have hp := mul_le_mul_of_nonneg_left hpow (mul_nonneg (pow_nonneg hr j) (pow_nonneg hs j))
    have hnr : r^n = r^j * r^(n-j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
    have hns : s^n = s^j * s^(n-j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
    rw [hnr, hns]
    nlinarith only [hp]
  rw [G_succ', G_succ']
  nlinarith only [hcross]

private lemma two_tier_bound (n : ℕ) (a b r s : ℝ)
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    a*(1-r) + r*b*(1-s^n) ≤
      max (a*(1-r^(n+1))) (b*(1-s^(n+1))) := by
  let M := max (a*(1-r^(n+1))) (b*(1-s^(n+1)))
  have hs0 : 0 ≤ s := hr.trans hrs
  have hr1 : r ≤ 1 := hrs.trans hs
  have hM : 0 ≤ M := (mul_nonneg ha (sub_nonneg.mpr (pow_le_one₀ hr hr1))).trans (le_max_left _ _)
  have hGr := G_pos n hr
  have hGs := G_pos n hs0
  let u := 1 / G (n+1) r
  let w := r * G n s / G (n+1) s
  have hu : 0 ≤ u := by positivity
  have hw : 0 ≤ w := div_nonneg (mul_nonneg hr (G_nonneg n hs0)) hGs.le
  have huw : u + w ≤ 1 := by
    dsimp [u,w]
    have hratio : G n s / G (n+1) s ≤ G n r / G (n+1) r :=
      (div_le_div_iff₀ hGs hGr).mpr (G_ratio n hr hrs)
    have h := mul_le_mul_of_nonneg_left hratio hr
    have hrec := G_succ n r
    have hmul : r * G n s / G (n+1) s ≤ r * G n r / G (n+1) r := by
      simpa [mul_div_assoc] using h
    calc
      1 / G (n+1) r + r * G n s / G (n+1) s
          ≤ 1 / G (n+1) r + r * G n r / G (n+1) r := add_le_add (le_refl _) hmul
      _ = 1 := by rw [← add_div, add_comm 1, ← hrec]; exact div_self (ne_of_gt hGr)
  have haeq : u * (a*(1-r^(n+1))) = a*(1-r) := by
    dsimp [u]
    rw [← G_mul (n+1) r]
    field_simp
  have hbeq : w * (b*(1-s^(n+1))) = r*b*(1-s^n) := by
    dsimp [w]
    rw [← G_mul (n+1) s, ← G_mul n s]
    field_simp
  calc
    a*(1-r) + r*b*(1-s^n) = u*(a*(1-r^(n+1))) + w*(b*(1-s^(n+1))) := by rw [haeq,hbeq]
    _ ≤ u*M + w*M := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hw)
    _ = (u+w)*M := by ring
    _ ≤ M := by simpa using mul_le_mul_of_nonneg_right huw hM

private def seqRevenue {n : ℕ} (p r : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, p i * (1-r i) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), r j

private lemma seqRevenue_succ (n : ℕ) (p r : Fin (n+1) → ℝ) :
    seqRevenue p r = p 0*(1-r 0) + r 0*seqRevenue (p ∘ Fin.succ) (r ∘ Fin.succ) := by
  classical
  unfold seqRevenue
  rw [Fin.sum_univ_succ]
  simp only [Finset.prod_filter]
  simp only [Fin.not_lt_zero, if_false, Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.prod_univ_succ]
  simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, Function.comp_apply]
  ring

private lemma ordered_bound (n : ℕ) (hn : 0 < n) (p r : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hmono : Monotone r) :
    ∃ i : Fin n, seqRevenue p r ≤ p i*(1-r i^n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      simp [seqRevenue]
    | succ n =>
      obtain ⟨i, hi⟩ := ih (by omega) (p ∘ Fin.succ) (r ∘ Fin.succ)
        (fun i => hp i.succ) (fun i => hr i.succ) (fun i => hr1 i.succ)
        (hmono.comp (fun i j hij => Fin.succ_le_succ_iff.mpr hij))
      have hfirst : seqRevenue p r ≤
          p 0*(1-r 0)+r 0*(p i.succ*(1-r i.succ^(n+1))) := by
        rw [seqRevenue_succ]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hi (hr 0))
      have htwo := two_tier_bound (n+1) (p 0) (p i.succ) (r 0) (r i.succ)
        (hp 0) (hp i.succ) (hr 0) (hmono (Fin.zero_le _)) (hr1 i.succ)
      have hmax : seqRevenue p r ≤
          max (p 0*(1-r 0^(n+1+1))) (p i.succ*(1-r i.succ^(n+1+1))) := by
        exact hfirst.trans (by simpa only [mul_assoc] using htwo)
      rcases le_max_iff.mp hmax with h | h
      · exact ⟨0,h⟩
      · exact ⟨i.succ,h⟩

end MinBuyingIIDProof

open MinBuyingIIDProof

theorem solution (n : ℕ) (hn : 0 < n) (F : Measure ℝ)
    (hF : ValidMarginal F) (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue (iidLaw n F) p ≤ uniformRevenue (iidLaw n F) (p i) := by
  classical
  haveI : IsProbabilityMeasure F := hF.1
  let σ := Tuple.sort p
  let q : Prices n := p ∘ σ
  have hq : FeasiblePrices q := fun i => hp (σ i)
  have hsorted : Monotone q := Tuple.monotone_sort p
  have hrej : Monotone (rejection F) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Iio_subset_Iio hab))
  have hrej0 : ∀ i : Fin n, 0 ≤ rejection F (q i) := fun _ => ENNReal.toReal_nonneg
  have hrej1 : ∀ i : Fin n, rejection F (q i) ≤ 1 := by
    intro i
    exact measureReal_le_one
  obtain ⟨i, hi⟩ := MinBuyingIIDProof.ordered_bound n hn q (fun i => rejection F (q i))
    hq hrej0 hrej1 (hrej.comp hsorted)
  have hformula := independent_revenue_formula n hn (fun _ => F) (fun _ => hF) q hq hsorted
  refine ⟨σ i, ?_⟩
  have hrev : Revenue (iidLaw n F) q = MinBuyingIIDProof.seqRevenue q (fun i => rejection F (q i)) :=
    hformula.1
  have hunif : uniformRevenue (iidLaw n F) (q i) = q i * (1-rejection F (q i)^n) := by
    simpa [iidLaw] using hformula.2 (q i) (hq i)
  rw [← hunif] at hi
  rw [← hrev] at hi
  have hperm := MinBuyingIIDProof.iid_revenue_permute F p σ
  exact hperm ▸ hi
