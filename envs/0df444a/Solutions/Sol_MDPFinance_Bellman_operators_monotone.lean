-- Prove2me | solution 1 for MDPFinance.Bellman.operators_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:34:32.621176+00:00
-- url     : https://prove2.me/submissions/2367fdd1-67f2-47d2-b99f-a5b091b6b57d

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

open MeasureTheory ProbabilityTheory MDPFinance.Bellman in
theorem erealIntegral_mono_727f81e8 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (v w : E → EReal) (hvw : ∀ x, v x ≤ w x) :
    erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  apply add_le_add
  · rw [EReal.coe_ennreal_le_coe_ennreal_iff]
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (hvw x) 0)
  · rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (hvw x)) 0)


open MeasureTheory ProbabilityTheory MDPFinance.Bellman in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (v w : E → EReal) (hv : v ∈ IM E) (hw : w ∈ IM E)
    (hvw : ∀ x, v x ≤ w x) :
    (∀ xa ∈ M.D n, L M n v xa ≤ L M n w xa) ∧
    (∀ f : E → A, ∀ x, Tf M n v f x ≤ Tf M n w f x) ∧
    (∀ x, T M n v x ≤ T M n w x) := by
  have hL : ∀ xa, L M n v xa ≤ L M n w xa := fun xa =>
    add_le_add le_rfl (erealIntegral_mono_727f81e8 _ v w hvw)
  refine ⟨fun xa _ => hL xa, fun f x => hL (x, f x), fun x => ?_⟩
  unfold T
  exact iSup₂_mono fun a _ => hL (x, a)

