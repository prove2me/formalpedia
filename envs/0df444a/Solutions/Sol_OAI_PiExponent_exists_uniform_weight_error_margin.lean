-- Prove2me | solution 1 for OAI.PiExponent.exists_uniform_weight_error_margin
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:16:52.115924+00:00
-- url     : https://prove2.me/submissions/9299ed7b-7e88-4ec8-8a0f-fdbceec122e7

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

section


namespace OAI

namespace PiExponent

theorem exists_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (_hΛ : 0 < Λ) (_hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ wstar : ℝ, X < wstar →
      Λ * (m : ℝ) / wstar + S / wstar < ε := by
  refine ⟨max 1 ((Λ * (m : ℝ) + S) / ε), le_max_left _ _, ?_⟩
  intro wstar hwstar
  have hwpos : 0 < wstar :=
    lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hwstar))
  have hquot : (Λ * (m : ℝ) + S) / ε < wstar :=
    lt_of_le_of_lt (le_max_right _ _) hwstar
  have hnum : Λ * (m : ℝ) + S < ε * wstar := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hquot
  rw [← add_div]
  exact (div_lt_iff₀ hwpos).mpr hnum

theorem reciprocal_sum_le_common_bound
    (m : ℕ) (w : Fin m → ℝ) (wstar : ℝ) (hwpos : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) :
    (∑ i : Fin m, 1 / w i) ≤ (m : ℝ) / wstar := by
  calc
    (∑ i : Fin m, 1 / w i) ≤ ∑ _i : Fin m, 1 / wstar := by
      apply Finset.sum_le_sum
      intro i _
      exact one_div_le_one_div_of_le hwpos (hw i)
    _ = (m : ℝ) / wstar := by simp [div_eq_mul_inv]





end PiExponent

end OAI

end


theorem solution
    (m : ℕ) (Λ S ε : ℝ) (hΛ : 0 < Λ) (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (wstar : ℝ) (w : Fin m → ℝ),
      X < wstar → (∀ i, wstar ≤ w i) →
      Λ * (∑ i : Fin m, 1 / w i) + S / wstar < ε := open OAI OAI.PiExponent in by
  obtain ⟨X, hX, hmargin⟩ := exists_weight_error_margin m Λ S ε hΛ hS hε
  refine ⟨X, hX, ?_⟩
  intro wstar w hwstar hw
  have hwpos : 0 < wstar := lt_trans zero_lt_one (lt_of_le_of_lt hX hwstar)
  have hsum := reciprocal_sum_le_common_bound m w wstar hwpos hw
  have hscaled := mul_le_mul_of_nonneg_left hsum hΛ.le
  have hsmall := hmargin wstar hwstar
  calc
    Λ * (∑ i : Fin m, 1 / w i) + S / wstar
        ≤ Λ * ((m : ℝ) / wstar) + S / wstar := add_le_add hscaled le_rfl
    _ = Λ * (m : ℝ) / wstar + S / wstar := by rw [mul_div_assoc]
    _ < ε := hsmall

#print axioms solution
