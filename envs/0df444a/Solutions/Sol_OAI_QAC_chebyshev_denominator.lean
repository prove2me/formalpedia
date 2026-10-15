-- Prove2me | solution 1 for OAI.QAC.chebyshev_denominator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:14:18.954628+00:00
-- url     : https://prove2.me/submissions/1ecc7bd9-a90f-40de-a681-19bb2598b5e0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean:L123-L162
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.chebyshev_denominator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial

-- ---- from OAI.InformationTheory.QuantumCircuit.Polynomial ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- An elementary hyperbolic lower bound for the Chebyshev denominator. -/
lemma chebyshev_denominator (k : ℕ) {m r : ℝ} (hr : 0 < r) (hm : r < m) :
    1 ≤ (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) ∧
    Real.exp ((k : ℝ) * Real.sqrt (r / m)) / 2 ≤
      (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) := by
  let q := Real.sqrt (r / m)
  have hm0 : 0 < m := lt_trans hr hm
  have hq0 : 0 < q := Real.sqrt_pos.2 (div_pos hr hm0)
  have hq1 : q < 1 := by
    dsimp [q]
    apply (Real.sqrt_lt' (by norm_num)).2
    simpa using (div_lt_one hm0).2 hm
  have hq2 : q ^ 2 = r / m := Real.sq_sqrt (le_of_lt (div_pos hr hm0))
  let h := (1 + q) / (1 - q)
  have hh0 : 0 < h := div_pos (by linarith) (by linarith)
  have hlog : q ≤ Real.log h := by
    dsimp [h]
    rw [Real.log_div (by linarith) (by linarith)]
    have hp := Real.log_nonneg (show 1 ≤ 1 + q by linarith)
    have hn := Real.log_le_sub_one_of_pos (show 0 < 1 - q by linarith)
    linarith
  have harg : (m + r) / (m - r) = Real.cosh (Real.log h) := by
    rw [Real.cosh_eq, Real.exp_log hh0, Real.exp_neg, Real.exp_log hh0]
    dsimp [h]
    have hqm : m * q ^ 2 = r := by nlinarith [((eq_div_iff (ne_of_gt hm0)).1 hq2)]
    have hmr : m - r ≠ 0 := by linarith
    have hqm1 : 1 - q ≠ 0 := by linarith
    have hqp1 : 1 + q ≠ 0 := by linarith
    field_simp [hmr, hqm1, hqp1]
    nlinarith
  rw [harg, Polynomial.Chebyshev.T_real_cosh]
  constructor
  · exact Real.one_le_cosh _
  · have he : Real.exp ((k : ℝ) * q) ≤ Real.exp ((k : ℤ) * Real.log h) := by
      apply Real.exp_le_exp.2
      norm_cast
      exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    rw [Real.cosh_eq]
    exact (div_le_div_of_nonneg_right he (by norm_num)).trans
      (by have := Real.exp_pos (-((k : ℤ) * Real.log h)); linarith)

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem solution (k : ℕ) {m r : ℝ} (hr : 0 < r) (hm : r < m) :
    1 ≤ (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) ∧
    Real.exp ((k : ℝ) * Real.sqrt (r / m)) / 2 ≤
      (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) := by
  first
    | exact OAI.QAC.chebyshev_denominator k hr hm
    | exact OAI.QAC.chebyshev_denominator
    | (apply OAI.QAC.chebyshev_denominator <;> assumption)
    | (intros; apply OAI.QAC.chebyshev_denominator <;> assumption)
