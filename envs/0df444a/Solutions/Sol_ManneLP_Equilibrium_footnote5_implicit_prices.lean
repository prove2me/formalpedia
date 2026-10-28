-- Prove2me | solution 1 for ManneLP.Equilibrium.footnote5_implicit_prices
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:13:13.454257+00:00
-- url     : https://prove2.me/submissions/0d017367-be31-4b34-bda3-bb7f9405e2cb

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example

open ManneLP.Equilibrium

namespace Aux_ManneLP_F5
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

end Aux_ManneLP_F5

theorem solution :
    let u : ℝ := 31 / 9
    let v : ℕ → ℝ := fun t =>
      if t = 1 then -7 / 3 else if t = 2 then -13 / 3 else if t = 3 then -11 / 3 else 0
    let e : ℕ × ℕ → ℕ × ℕ → ℝ := fun a b => if b = a then 1 else 0
    let reduced : ℕ × ℕ → ℝ := fun a =>
      u + ∑ t ∈ Finset.Icc 1 3,
        v t * (marginal exampleModel (e a) t - rhsPos exampleModel (e a) t)
    (∀ a ∈ exampleModel.A, reduced a ≤ costCoeff exampleModel a.1 a.2) ∧
    (∀ a ∈ ({(0, 1), (1, 1), (2, 0), (3, 0)} : Finset (ℕ × ℕ)),
      reduced a = costCoeff exampleModel a.1 a.2) ∧
    u = lpObj exampleModel exampleOptimal := by
  open Aux_ManneLP_F5 in
  intro u v e reduced
  have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have key : ∀ a, reduced a = u + v 1 * (e a (1,0) + e a (1,1) - (2/3 * (e a (0,1) + e a (1,0)) + 1/3 * (e a (2,1) + e a (3,0))))
      + v 2 * (e a (2,0) + e a (2,1) - 2/3 * (e a (1,1) + e a (2,0)))
      + v 3 * (e a (3,0) - 2/3 * (e a (2,1) + e a (3,0))) := by
    intro a
    simp only [reduced]
    rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      marg1, marg2, marg3, rhs1, rhs2, rhs3]
    ring
  refine ⟨fun a ha => ?_, fun a ha => ?_, ?_⟩
  · rw [key, cc]
    rw [hA] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [e, v, u] <;> norm_num
  · rw [key, cc]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [e, v, u] <;> norm_num
  · rw [obj]; simp [exampleOptimal, u]; norm_num
