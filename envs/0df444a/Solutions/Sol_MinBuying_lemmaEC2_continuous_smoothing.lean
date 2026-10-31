-- Prove2me | solution 1 for MinBuying.lemmaEC2_continuous_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:52:01.276866+00:00
-- url     : https://prove2.me/submissions/e5f0d938-e303-4b53-9384-78ad9abcbb34

import Theorems.Thm_MinBuying_triangular_continuous_smoothing
import Theorems.Thm_MinBuying_triangular_wellposed
import Theorems.Thm_MinBuying_triangular_law_specification
import Theorems.Thm_MinBuying_independent_revenue_formula
import Theorems.Thm_MinBuying_bounded_continuous_wellposed

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

private lemma uniform_formula {n : ℕ} (hn : 0 < n) (F : Fin n → Measure ℝ)
    (hF : ∀ i, ValidMarginal (F i)) (q : ℝ) (hq : 0 ≤ q) :
    uniformRevenue (productLaw F) q = q * (1 - ∏ i, rejection (F i) q) :=
  (independent_revenue_formula n hn F hF (fun _ => 0) (fun _ => le_rfl) monotone_const).2 q hq

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

private lemma same_rejection_revenue {n : ℕ} (hn : 0 < n)
    (F G : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (hG : ∀ i, ValidMarginal (G i)) (p : Prices n) (hp : FeasiblePrices p)
    (heq : ∀ i, rejection (G i) (p i) = rejection (F i) (p i)) :
    Revenue (productLaw G) p = Revenue (productLaw F) p := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1
  letI (i : Fin n) : IsProbabilityMeasure (G i) := (hG i).1
  let σ := Tuple.sort p
  rw [← revenue_permute F p σ, ← revenue_permute G p σ]
  rw [(independent_revenue_formula n hn (G ∘ σ) (fun i => hG (σ i))
      (p ∘ σ) (fun i => hp (σ i)) (Tuple.monotone_sort p)).1,
    (independent_revenue_formula n hn (F ∘ σ) (fun i => hF (σ i))
      (p ∘ σ) (fun i => hp (σ i)) (Tuple.monotone_sort p)).1]
  simp only [independentRevenueFormula, Function.comp_apply, heq]

private lemma uniform_smoothing_bound {n : ℕ} (hn : 0 < n) (I : TriangularInstance n)
    (hUP : UPRevenue (triangularJoint I) ≤ 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (F : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (hshift : ∀ i p, rejection (triangularLaw (I.a i) (I.cap i)) (p-δ) ≤ rejection (F i) p) :
    UPRevenue (productLaw F) ≤ 1/(1-δ) := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1
  have hT (i : Fin n) : ValidMarginal (triangularMarginals I i) :=
    (triangular_law_specification (I.a i) (I.cap i) (I.a_pos i) (I.cap_pos i)).1
  letI (i : Fin n) : IsProbabilityMeasure (triangularMarginals I i) := (hT i).1
  have hW := (triangular_wellposed n hn I).2
  have hd : 0 < 1-δ := sub_pos.mpr hδ1
  have hunit : 1 ≤ 1/(1-δ) := (le_div_iff₀ hd).mpr (by linarith)
  have hb (p : ℝ) (hp : 0 ≤ p) : uniformRevenue (productLaw F) p ≤ 1/(1-δ) := by
    rw [uniform_formula hn F hF p hp]
    have hP0 : 0 ≤ ∏ i, rejection (F i) p :=
      Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    by_cases hp1 : p ≤ 1
    · have hh : p*(1-∏ i, rejection (F i) p) ≤ p := by nlinarith
      exact hh.trans (hp1.trans hunit)
    · have hp1' : 1 < p := lt_of_not_ge hp1
      have hq : 0 < p-δ := by linarith
      have hP : ∏ i, rejection (triangularMarginals I i) (p-δ) ≤
          ∏ i, rejection (F i) p := by
        apply Finset.prod_le_prod
        · intro i _
          exact ENNReal.toReal_nonneg
        · intro i _
          exact hshift i p
      have hPl : ∏ i, rejection (triangularMarginals I i) (p-δ) ≤ 1 := by
        apply Finset.prod_le_one
        · intro i _
          exact ENNReal.toReal_nonneg
        · intro i _
          exact measureReal_le_one
      have hA : 0 ≤ 1-∏ i, rejection (triangularMarginals I i) (p-δ) := sub_nonneg.mpr hPl
      have hOld : (p-δ)*(1-∏ i, rejection (triangularMarginals I i) (p-δ)) ≤ 1 := by
        rw [← uniform_formula hn (triangularMarginals I) hT (p-δ) hq.le]
        exact (le_csSup hW.2.1 ⟨p-δ,hq.le,rfl⟩).trans hUP
      have hfac : p*(1-δ) ≤ p-δ := by nlinarith
      have hbound : p*(1-∏ i, rejection (triangularMarginals I i) (p-δ)) ≤ 1/(1-δ) := by
        apply (le_div_iff₀ hd).mpr
        have hh := mul_le_mul_of_nonneg_right hfac hA
        nlinarith
      apply le_trans ?_ hbound
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hP 1) hp
  change sSup (uniformValues (productLaw F)) ≤ _
  apply csSup_le (show (uniformValues (productLaw F)).Nonempty from
    ⟨uniformRevenue (productLaw F) 0, 0, le_rfl, rfl⟩)
  rintro r ⟨p,hp,rfl⟩
  exact hb p hp

theorem solution (n : ℕ) (hn : 0 < n)
    (I : TriangularInstance n) (hUP : UPRevenue (triangularJoint I) ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < min 1 δ₀ →
      ∃ F : Fin n → Measure ℝ,
        RegularInstance F ∧
        Revenue (productLaw F) I.cap = Revenue (triangularJoint I) I.cap ∧
        UPRevenue (productLaw F) ≤ 1 / (1 - δ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨i, _, hmin⟩ := Finset.univ.exists_min_image I.a Finset.univ_nonempty
  refine ⟨I.a i, I.a_pos i, ?_⟩
  intro δ hδ hδm
  have hδ1 : δ < 1 := (lt_min_iff.mp hδm).1
  have hδa (j : Fin n) : δ < I.a j :=
    ((lt_min_iff.mp hδm).2).trans_le (hmin j (Finset.mem_univ _))
  choose F hF hs hcap hshift using fun j =>
    triangular_continuous_smoothing (I.a j) (I.cap j) δ (I.a_pos j) (I.cap_pos j) hδ (hδa j)
  let M := (∑ j, I.cap j) + δ
  have hM (j : Fin n) : ∀ᵐ x ∂F j, x ≤ M := by
    filter_upwards [hs j] with x hx
    have hj : I.cap j ≤ ∑ k, I.cap k :=
      Finset.single_le_sum (fun k _ => (I.cap_pos k).le) (Finset.mem_univ j)
    exact hx.2.trans (by dsimp [M]; linarith)
  have hW := bounded_continuous_wellposed n hn F (fun j => (hF j).1)
    (fun j => (hF j).2.1) M hM
  refine ⟨F, ⟨hn,hF,hW⟩, ?_,
    uniform_smoothing_bound hn I hUP δ hδ hδ1 F (fun j => (hF j).1) hshift⟩
  exact same_rejection_revenue hn (triangularMarginals I) F
    (fun j => (triangular_law_specification _ _ (I.a_pos j) (I.cap_pos j)).1)
    (fun j => (hF j).1) I.cap (fun j => (I.cap_pos j).le) hcap

