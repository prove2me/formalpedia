-- Prove2me | solution 1 for MultiPurchaseMNL.removal_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:31:54.187925+00:00
-- url     : https://prove2.me/submissions/28b56c40-36bd-4691-b031-cdceebc35842

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model

open MeasureTheory ProbabilityTheory

open MultiPurchaseMNL in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] {n mmax : ℕ}
    (I : Instance n mmax) (m : ℕ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (ℓ : Fin n)
    (hℓ : ℓ ∈ S.erase i) :
    piM μ I m i S ≤ piM μ I m i (S.erase ℓ) := by
  unfold piM
  have hsub : {e | rank I S i e ≤ m ∧ utility I e none < utility I e (some i)} ⊆
      {e | rank I (S.erase ℓ) i e ≤ m ∧ utility I e none < utility I e (some i)} := by
    rintro e ⟨h1, h2⟩
    refine ⟨le_trans ?_ h1, h2⟩
    unfold rank
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
  haveI : IsProbabilityMeasure (shockLaw μ n) := by
    unfold shockLaw; infer_instance
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
