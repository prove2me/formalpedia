-- Prove2me | solution 1 for GreshamLaw.sixpence_single_coin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:19:41.476403+00:00
-- url     : https://prove2.me/submissions/f5d64423-5301-4e51-a3b0-69a025c30d86

import Mathlib
import Definitions.Def_GreshamLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open GreshamLaw

theorem solution {ι : Type*} [DecidableEq ι] (coin : ι → Coin) (s : Finset ι)
    (hlegal : EqualLegalTender coin s)
    (hpos : ∀ i ∈ s, 0 < (coin i).face) (c : ι) :
    IsOptimalPayment coin s {c} (coin c).face ↔
      c ∈ s ∧ ∀ j ∈ s, (coin c).melt ≤ (coin j).melt := by
  classical
  have hret : ∀ i ∈ s,
      totalMelt coin (s \ {i}) = totalMelt coin s - (coin i).melt := by
    intro i hi
    simp [totalMelt, Finset.sdiff_singleton_eq_erase,
      Finset.sum_erase_eq_sub, hi]
  constructor
  · rintro ⟨⟨hcsub, hface⟩, hoptimal⟩
    have hc : c ∈ s := Finset.singleton_subset_iff.mp hcsub
    refine ⟨hc, ?_⟩
    intro j hj
    have hjlegal : IsLegalPayment coin s {j} (coin c).face := by
      refine ⟨Finset.singleton_subset_iff.mpr hj, ?_⟩
      simp [totalFace, hlegal j hj c hc]
    have hineq := hoptimal {j} hjlegal
    rw [hret j hj, hret c hc] at hineq
    linarith
  · rintro ⟨hc, hminimal⟩
    have hsingle : IsLegalPayment coin s {c} (coin c).face := by
      exact ⟨Finset.singleton_subset_iff.mpr hc, by simp [totalFace]⟩
    refine ⟨hsingle, ?_⟩
    intro Q hQ
    rcases hQ with ⟨hQs, hQd⟩
    have hQsame : ∀ j ∈ Q, (coin j).face = (coin c).face := by
      intro j hj
      exact hlegal j (hQs hj) c hc
    have hQcardreal : (Q.card : ℝ) = 1 := by
      have hsum : (Q.card : ℝ) * (coin c).face = (coin c).face := by
        calc
          (Q.card : ℝ) * (coin c).face =
              ∑ j ∈ Q, (coin c).face := by simp
          _ = totalFace coin Q := by
            unfold totalFace
            apply Finset.sum_congr rfl
            intro j hj
            exact (hQsame j hj).symm
          _ = (coin c).face := hQd
      have hprod : ((Q.card : ℝ) - 1) * (coin c).face = 0 := by
        nlinarith [hsum]
      have hzero : (Q.card : ℝ) - 1 = 0 :=
        (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (hpos c hc))
      linarith
    have hQcard : Q.card = 1 := by exact_mod_cast hQcardreal
    obtain ⟨j, hjQ⟩ := Finset.card_eq_one.mp hQcard
    have hj : j ∈ s := hQs (by rw [hjQ]; simp)
    have hineq : totalMelt coin (s \ {j}) ≤ totalMelt coin (s \ {c}) := by
      rw [hret j hj, hret c hc]
      linarith [hminimal j hj]
    simpa [hjQ] using hineq
