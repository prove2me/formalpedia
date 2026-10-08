-- Prove2me | solution 1 for LeviBalancing.TripleBalancing.no_backorders_after_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:40:48.407782+00:00
-- url     : https://prove2.me/submissions/b47aa0b6-ef55-4c09-bd67-e31e42efbdad

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory


namespace LeviBalancing.TripleBalancing

theorem nbo_core {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) :
    ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < TB s ω → M.D s ω ≤ levelAfter M TB s ω := by
  intro s hs ω hpos
  obtain ⟨_, hrule⟩ := hTB
  obtain ⟨h1, h2⟩ := hrule s hs ω
  have hsT : s ≤ M.T := (Finset.mem_Icc.mp hs).2
  by_cases hK : accBacklog M TB s ω ≤ M.K
  · have := h1 hK; linarith
  rw [not_le] at hK
  obtain ⟨h3, h4⟩ := h2 hK
  unfold levelAfter
  rcases lt_or_eq_of_le hsT with hlt | heq
  · have hG := h3 hlt
    set x := levelBefore M TB s ω with hx
    set q0 := max (M.D s ω - x) 0 with hq0
    have hmem : q0 ∈ {q : ℝ | 0 ≤ q ∧ condMarginalHolding M I TB s q ω ≤ ENNReal.ofReal M.K} := by
      refine ⟨le_max_right _ _, ?_⟩
      have hzero : condMarginalHolding M I TB s q0 ω = 0 := by
        unfold condMarginalHolding
        rw [← hx]
        have hae : ∀ᵐ d ∂(I s ω), ENNReal.ofReal (marginalHolding M s q0 x d) = 0 := by
          filter_upwards [hI.2.2.2.1 s ω, hI.2.2.2.2.1 s ω] with d hds hdn
          apply ENNReal.ofReal_eq_zero.mpr
          unfold marginalHolding
          apply Finset.sum_nonpos
          intro j hj
          have hsj : s ≤ j := (Finset.mem_Icc.mp hj).1
          have hsum : d s ≤ ∑ i ∈ Finset.Icc s j, d i :=
            Finset.single_le_sum (f := d) (fun i _ => hdn i)
              (Finset.mem_Icc.mpr ⟨le_rfl, hsj⟩)
          have : max (q0 - max ((∑ i ∈ Finset.Icc s j, d i) - x) 0) 0 = 0 := by
            apply max_eq_right
            rw [hq0, hds] at *
            have : M.D s ω - x ≤ (∑ i ∈ Finset.Icc s j, d i) - x := by linarith
            have := max_le_max this (le_refl (0:ℝ))
            linarith
          rw [this, mul_zero]
        rw [lintegral_congr_ae hae, lintegral_zero]
      rw [hzero]; exact bot_le
    have hle := hG.2 hmem
    have : M.D s ω - x ≤ q0 := le_max_left _ _
    linarith
  · rw [h4 heq]; linarith

end LeviBalancing.TripleBalancing

open LeviBalancing.TripleBalancing


theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) :
    ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < TB s ω → M.D s ω ≤ levelAfter M TB s ω := by
  exact nbo_core M I hI TB hTB
