-- Prove2me | solution 1 for MinBuying.theorem3_exchangeable_gap
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:38:48.018979+00:00
-- url     : https://prove2.me/submissions/97b5bea7-dd84-4bf2-934a-634fbf14364f

import Theorems.Thm_MinBuying_finite_support_wellposed
import Theorems.Thm_MinBuying_exchangeable_subset_bound
import Theorems.Thm_MinBuying_exchangeable_construction_valid
import Theorems.Thm_MinBuying_exchangeable_construction_revenue

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section

theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ μ : JointLaw n, ValidLaw μ ∧ Exchangeable μ ∧ WellPosed μ ∧
      (3 / 32 : ℝ) * Real.log (n : ℝ) * UPRevenue μ ≤ DPRevenue μ := by
  classical
  obtain ⟨hvalid,hex,⟨S,hS⟩⟩ := exchangeable_construction_valid n
  obtain ⟨hu,hpos,hd⟩ := exchangeable_construction_revenue n hn
  have hw : WellPosed (exchangeableGapLaw n) :=
    finite_support_wellposed n _ hvalid.1 S hS ⟨2,by norm_num,hpos⟩
  refine ⟨exchangeableGapLaw n,hvalid,hex,hw,?_⟩
  have hup : UPRevenue (exchangeableGapLaw n) ≤ 1 := by
    apply csSup_le
    · exact ⟨uniformRevenue (exchangeableGapLaw n) 0,0,le_rfl,rfl⟩
    · rintro r ⟨q,hq,rfl⟩
      exact hu q hq
  have hdp : Revenue (exchangeableGapLaw n) (gapPrices n) ≤
      DPRevenue (exchangeableGapLaw n) := by
    apply le_csSup hw.1
    exact ⟨gapPrices n,fun i => by unfold gapPrices;positivity,rfl⟩
  have hratio : ∀ i : Fin n,
      1 / (4*((i.val+1 : ℕ) : ℝ)) ≤
      ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
        (n.choose (gapTypeSize n i) : ℝ) := by
    intro i
    have hi := i.isLt
    have ht : n-1-i.val < n := by omega
    have heq : n-(n-1-i.val) = i.val+1 := by omega
    simpa [heq,gapTypeSize] using exchangeable_subset_bound n (n-1-i.val) hn ht
  have hsum : (3/32:ℝ) * (harmonic n : ℝ) ≤
      (3/8:ℝ) * (∑ i : Fin n, ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
        (n.choose (gapTypeSize n i) : ℝ)) := by
    have hh : (harmonic n : ℝ) = ∑ i : Fin n, 1/((i.val+1 : ℕ) : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => 1/((j+1 : ℕ) : ℝ))]
      simp [harmonic,Rat.cast_sum,Rat.cast_inv]
    rw [hh]
    calc
      (3/32:ℝ) * (∑ i : Fin n, 1/((i.val+1 : ℕ) : ℝ))
          = (3/8:ℝ) * (∑ i : Fin n, 1/(4*((i.val+1 : ℕ) : ℝ))) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hratio i)) (by norm_num)
  have hlog : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
    simpa using log_le_harmonic_floor (n : ℝ) (by positivity)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hn
  calc
    (3/32:ℝ) * Real.log (n : ℝ) * UPRevenue (exchangeableGapLaw n)
        ≤ (3/32:ℝ)*Real.log (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hup (mul_nonneg (by norm_num) hlog_nonneg)
    _ ≤ (3/32:ℝ)*(harmonic n : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ _ := hsum.trans (hd.trans hdp)
