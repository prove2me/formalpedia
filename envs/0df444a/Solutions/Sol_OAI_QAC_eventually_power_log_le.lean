-- Prove2me | solution 1 for OAI.QAC.eventually_power_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:18.190649+00:00
-- url     : https://prove2.me/submissions/b6d4cd5b-f2ea-4688-989b-a64b31a16e8d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Asymptotics.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.eventually_power_log_le. The node keeps its source
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

-- ---- from OAI.InformationTheory.QuantumCircuit.Asymptotics ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- The same strict gap absorbs a logarithm, with no change to the exponent. -/
lemma eventually_power_log_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s * Real.log N ≤ (N : ℝ) ^ t := by
  have h := ((isLittleO_log_rpow_atTop (sub_pos.2 hst)).const_mul_left C).bound
    (c := 1) zero_lt_one
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : C * Real.log N ≤ (N : ℝ) ^ (t - s) := by
    have hN' : |C * Real.log N| ≤ (N : ℝ) ^ (t - s) := by
      simpa only [Real.norm_eq_abs, one_mul,
        abs_of_nonneg (Real.rpow_nonneg hN0.le (t - s))] using hN
    exact (le_abs_self _).trans hN'
  calc
    C * (N : ℝ) ^ s * Real.log N = (C * Real.log N) * (N : ℝ) ^ s := by ring
    _ ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem solution {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s * Real.log N ≤ (N : ℝ) ^ t := by
  first
    | exact OAI.QAC.eventually_power_log_le hst C
    | exact OAI.QAC.eventually_power_log_le
    | (apply OAI.QAC.eventually_power_log_le <;> assumption)
    | (intros; apply OAI.QAC.eventually_power_log_le <;> assumption)
