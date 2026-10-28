-- Prove2me | solution 1 for ManneLP.Equilibrium.table2_optimal_solution
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:10:57.043143+00:00
-- url     : https://prove2.me/submissions/5e6728d1-e59d-4468-8f18-49426068ee4d

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example

open ManneLP.Equilibrium

namespace Aux_ManneLP_T2
open ManneLP.Equilibrium

theorem hA : exampleModel.A = {(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)} := by
  decide

theorem tsumP (f : ℕ → ℝ) : ∑' n, exampleModel.p n * f n = 2/3 * f 0 + 1/3 * f 2 := by
  rw [tsum_eq_sum (s := {0, 2})]
  · rw [Finset.sum_pair (by norm_num)]
    simp [exampleModel, exampleDemand]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [exampleModel, exampleDemand, hn.1, hn.2]

theorem tsumI (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    ∑' n, (if P n then exampleModel.p n * c else 0)
      = (if P 0 then 2/3*c else 0) + (if P 2 then 1/3*c else 0) := by
  rw [tsum_eq_sum (s := {0, 2})]
  · rw [Finset.sum_pair (by norm_num)]
    simp [exampleModel, exampleDemand]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [exampleModel, exampleDemand, hn.1, hn.2]

theorem act (t : ℕ) : actions exampleModel t =
    (Finset.range 4).filter (fun j => (t, j) ∈ exampleModel.A) := rfl



theorem sumA (g : ℕ × ℕ → ℝ) : ∑ a ∈ exampleModel.A, g a =
    g (0,0) + g (0,1) + g (1,0) + g (1,1) + g (2,0) + g (2,1) + g (3,0) := by
  rw [hA]
  simp [Finset.sum_insert]
  ring

theorem marg1 (x : ℕ × ℕ → ℝ) : marginal exampleModel x 1 = x (1,0) + x (1,1) := by
  have : actions exampleModel 1 = {0, 1} := by rw [act, hA]; decide
  simp [marginal, this]

theorem marg2 (x : ℕ × ℕ → ℝ) : marginal exampleModel x 2 = x (2,0) + x (2,1) := by
  have : actions exampleModel 2 = {0, 1} := by rw [act, hA]; decide
  simp [marginal, this]

theorem marg3 (x : ℕ × ℕ → ℝ) : marginal exampleModel x 3 = x (3,0) := by
  have : actions exampleModel 3 = {0} := by rw [act, hA]; decide
  simp [marginal, this]

theorem marg0 (x : ℕ × ℕ → ℝ) : marginal exampleModel x 0 = x (0,0) + x (0,1) := by
  have : actions exampleModel 0 = {0, 1} := by rw [act, hA]; decide
  simp [marginal, this]

theorem rhs (x : ℕ × ℕ → ℝ) (t : ℕ) : rhsPos exampleModel x t =
    ∑ a ∈ exampleModel.A, ((if (a.1 : ℤ) + (a.2 : ℤ) - 0 = (t : ℤ) then 2/3 * x a else 0)
      + (if (a.1 : ℤ) + (a.2 : ℤ) - 2 = (t : ℤ) then 1/3 * x a else 0)) := by
  unfold rhsPos
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tsumI]
  push_cast
  rfl

theorem rhs1 (x : ℕ × ℕ → ℝ) : rhsPos exampleModel x 1 =
    2/3 * (x (0,1) + x (1,0)) + 1/3 * (x (2,1) + x (3,0)) := by
  rw [rhs, sumA]; norm_num; ring

theorem rhs2 (x : ℕ × ℕ → ℝ) : rhsPos exampleModel x 2 = 2/3 * (x (1,1) + x (2,0)) := by
  rw [rhs, sumA]; norm_num; ring

theorem rhs3 (x : ℕ × ℕ → ℝ) : rhsPos exampleModel x 3 = 2/3 * (x (2,1) + x (3,0)) := by
  rw [rhs, sumA]; norm_num; ring

theorem cc (i j : ℕ) : costCoeff exampleModel i j =
    (i : ℝ) + 3 * j + 2/3 * max 0 (6 * ((0:ℝ) - i - j)) + 1/3 * max 0 (6 * ((2:ℝ) - i - j)) := by
  unfold costCoeff
  rw [tsumP]
  simp [exampleModel]
  ring

theorem obj (x : ℕ × ℕ → ℝ) : lpObj exampleModel x =
    4 * x (0,0) + 5 * x (0,1) + 3 * x (1,0) + 4 * x (1,1) + 2 * x (2,0) + 5 * x (2,1) + 3 * x (3,0) := by
  unfold lpObj
  rw [sumA]
  simp only [cc]
  norm_num

end Aux_ManneLP_T2

theorem solution :
    IsLPOptimal exampleModel exampleOptimal ∧ lpObj exampleModel exampleOptimal = 31 / 9 ∧
    (decodeRule exampleModel exampleOptimal 0 0 = 0 ∧ decodeRule exampleModel exampleOptimal 0 1 = 1 ∧
      decodeRule exampleModel exampleOptimal 1 0 = 0 ∧ decodeRule exampleModel exampleOptimal 1 1 = 1 ∧
      decodeRule exampleModel exampleOptimal 2 0 = 1 ∧ decodeRule exampleModel exampleOptimal 2 1 = 0) ∧
    IsLPFeasible exampleModel exampleDoNothing ∧ lpObj exampleModel exampleDoNothing = 4 := by
  open Aux_ManneLP_T2 in
  have feas : ∀ x : ℕ × ℕ → ℝ, (∀ a ∈ exampleModel.A, 0 ≤ x a) →
      x (0,0) + x (0,1) + x (1,0) + x (1,1) + x (2,0) + x (2,1) + x (3,0) = 1 →
      x (1,0) + x (1,1) = 2/3 * (x (0,1) + x (1,0)) + 1/3 * (x (2,1) + x (3,0)) →
      x (2,0) + x (2,1) = 2/3 * (x (1,1) + x (2,0)) →
      x (3,0) = 2/3 * (x (2,1) + x (3,0)) → IsLPFeasible exampleModel x := by
    intro x h0 hs e1 e2 e3
    refine ⟨h0, by rw [sumA]; exact hs, fun t ht1 ht3 => ?_⟩
    have ht3' : t ≤ 3 := ht3
    interval_cases t
    · show marginal _ _ _ = rhsPos _ _ _
      rw [marg1, rhs1]; exact e1
    · show marginal _ _ _ = rhsPos _ _ _
      rw [marg2, rhs2]; exact e2
    · show marginal _ _ _ = rhsPos _ _ _
      rw [marg3, rhs3]; exact e3
  have hopt : IsLPFeasible exampleModel exampleOptimal := by
    apply feas
    · intro a _
      simp only [exampleOptimal]
      split_ifs <;> norm_num
    all_goals (simp [exampleOptimal] <;> norm_num)
  have hdn : IsLPFeasible exampleModel exampleDoNothing := by
    apply feas
    · intro a _
      simp only [exampleDoNothing]
      split_ifs <;> norm_num
    all_goals simp [exampleDoNothing]
  have hobj : lpObj exampleModel exampleOptimal = 31 / 9 := by
    rw [obj]; simp [exampleOptimal]; norm_num
  refine ⟨⟨hopt, fun x' hx' => ?_⟩, hobj, ?_, hdn, ?_⟩
  · obtain ⟨h0, hs, h8⟩ := hx'
    rw [sumA] at hs
    have hT : exampleModel.T = 3 := rfl
    have e1 := h8 1 le_rfl (by rw [hT]; norm_num)
    have e2 := h8 2 (by norm_num) (by rw [hT]; norm_num)
    have e3 := h8 3 (by norm_num) (by rw [hT])
    unfold Eq8t at e1 e2 e3
    rw [marg1, rhs1] at e1
    rw [marg2, rhs2] at e2
    rw [marg3, rhs3] at e3
    have p00 := h0 (0,0) (by rw [hA]; simp)
    have p01 := h0 (0,1) (by rw [hA]; simp)
    have p10 := h0 (1,0) (by rw [hA]; simp)
    have p11 := h0 (1,1) (by rw [hA]; simp)
    have p20 := h0 (2,0) (by rw [hA]; simp)
    have p21 := h0 (2,1) (by rw [hA]; simp)
    have p30 := h0 (3,0) (by rw [hA]; simp)
    rw [hobj, obj]
    linarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [decodeRule, marg0, marg1, marg2, hA, exampleOptimal] <;> norm_num
  · rw [obj]; simp [exampleDoNothing]
