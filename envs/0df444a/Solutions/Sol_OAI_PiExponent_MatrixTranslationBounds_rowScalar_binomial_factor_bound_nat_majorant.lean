-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_nat_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:45:43.738757+00:00
-- url     : https://prove2.me/submissions/d660c878-e3bd-48b9-b9ac-60ed792aca9d

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) :
    ‖((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      (4 : ℝ) ^ (∑ i, a i) := by
  have hprod :
      (∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) ≤
        4 ^ (∑ i, a i) := by
    calc
      (∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) ≤
          ∏ i, (2 ^ (a i) * 2 ^ (a i)) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact Nat.zero_le _
            · intro i hi
              have h₁ : (a i).choose (β i) ≤ 2 ^ (a i) :=
                Nat.choose_le_two_pow (a i) (β i)
              have h₂ : (a i - β i).choose (d i) ≤ 2 ^ (a i - β i) :=
                Nat.choose_le_two_pow (a i - β i) (d i)
              have h₃ : 2 ^ (a i - β i) ≤ 2 ^ (a i) := by
                gcongr
                · norm_num
                · exact Nat.sub_le _ _
              exact Nat.mul_le_mul h₁ (h₂.trans h₃)
      _ = ∏ i, 4 ^ (a i) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [← mul_pow]
            norm_num
      _ = 4 ^ (∑ i, a i) := by
            exact Finset.prod_pow_eq_pow_sum Finset.univ a (4 : ℕ)
  have hcast :
      (↑(∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℝ) ≤
        (4 : ℝ) ^ (∑ i, a i) := by
    exact_mod_cast hprod
  simpa using hcast