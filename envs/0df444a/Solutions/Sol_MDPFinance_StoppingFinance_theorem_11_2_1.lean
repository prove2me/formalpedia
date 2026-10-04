-- Prove2me | solution 1 for MDPFinance.StoppingFinance.theorem_11_2_1
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:28:15.843868+00:00
-- url     : https://prove2.me/submissions/9cf270c9-73ae-45da-880d-a95abf27d197

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_CreditModel

open MeasureTheory MDPFinance.StoppingFinance

namespace CreditCex

noncomputable def cc (x : ℝ) : ℝ := if 0 < x then 1 else -1

theorem cc_mono : Monotone cc := by
  intro x y hxy
  unfold cc
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 hxy) h2
  · norm_num
  · exact le_rfl

noncomputable def M0 : CreditModel where
  QX := fun _ => Measure.dirac 0
  QX_prob := fun _ => inferInstance
  QX_meas := measurable_const
  c := cc
  c_meas := by
    unfold cc
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  beta := 1
  beta_mem := by norm_num
  hbound := ⟨fun _ => 1, 1, 1, measurable_const, fun _ => zero_le_one, zero_le_one,
    fun x => by unfold cc; split_ifs <;> norm_num, fun x => by simp⟩

theorem hM : M0.StructuralAssumptions := by
  refine ⟨cc_mono, fun v _ _ _ => ?_⟩
  intro x y _
  show ∫ z, v z ∂(Measure.dirac 0) ≤ ∫ z, v z ∂(Measure.dirac 0)
  exact le_rfl

theorem cbar1 (x : ℝ) : M0.cbar 1 x = cc x := by
  show cc x + 1 * ∫ y, M0.J 0 y ∂(Measure.dirac 0) = cc x
  simp [CreditModel.J]

end CreditCex

open CreditCex in
theorem solution : ¬ (∀ (M : CreditModel) (hM : M.StructuralAssumptions) (N : ℕ),
    (∀ n : ℕ, Monotone (M.J n)) ∧
    (∀ (m n : ℕ), m ≤ n → ∀ x : ℝ, M.J m x ≤ M.J n x) ∧
    (∃ xstar : ℕ → EReal,
      (∀ (m n : ℕ), 1 ≤ m → m ≤ n → n ≤ N → xstar n ≤ xstar m) ∧
      (∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N → (M.cbar n x < 0 ↔ (x : EReal) < xstar n)) ∧
      ∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N →
        (if (x : EReal) < xstar n then 0 else M.cbar n x) = M.J n x)) := by
  intro h
  obtain ⟨_, _, xs, _, hx, _⟩ := h M0 hM 1
  have h0 : ((0 : ℝ) : EReal) < xs 1 := by
    rw [← hx 1 0 le_rfl le_rfl, cbar1]
    simp [cc]
  obtain ⟨z, hz0, hz1⟩ := EReal.lt_iff_exists_real_btwn.mp h0
  have := (hx 1 z le_rfl le_rfl).mpr hz1
  rw [cbar1] at this
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz0
  simp [cc, hzpos] at this
  linarith

#print axioms solution
