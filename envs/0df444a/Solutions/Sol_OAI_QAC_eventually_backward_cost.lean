-- Prove2me | solution 1 for OAI.QAC.eventually_backward_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:56.185998+00:00
-- url     : https://prove2.me/submissions/35d3a05b-3b95-4880-a017-277b2f0b25a6

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Asymptotics.lean:L260-L283
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.eventually_backward_cost. The node keeps its source
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

/-- Strict exponent gaps absorb every fixed multiplicative constant. -/
lemma eventually_power_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s ≤ (N : ℝ) ^ t := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (t - s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hst)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    C * (N : ℝ) ^ s ≤ (N : ℝ) ^ (t - s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ t := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- Every fixed coefficient and prefactor is absorbed by the strict power gaps. -/
lemma eventually_exp_power_gap {s u v : ℝ} (hs : s < v) (hu : u < v) (hv : 0 < v)
    (C ε D K : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * Real.exp (K*(N:ℝ)^u - (N:ℝ)^v) ≤
      ε * Real.exp (-(D*(N:ℝ)^s)) := by
  filter_upwards [eventually_power_le hv (3*Real.log (C/ε)),
    eventually_power_le hu (3*K),eventually_power_le hs (3*D)] with N h0 h1 h2
  simp only [Real.rpow_zero,mul_one] at h0
  calc
    _ = ε * Real.exp (Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v) := by
      rw [show Real.log (C/ε) + K*(N:ℝ)^u - (N:ℝ)^v =
        Real.log (C/ε) + (K*(N:ℝ)^u - (N:ℝ)^v) by ring, Real.exp_add,
        Real.exp_log (div_pos hC hε)]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [h0,h1,h2])) hε.le

lemma eventually_backward_cost {s a u w t : ℝ} (hs : 0 ≤ s) (hsa : s < a)
    (hau : a < u) (huw : u < w) (hwt : w < t) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) + Real.exp (-((N:ℝ)^a)) +
        (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤ Real.exp (-2*(N:ℝ)^s) := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hsu := hsa.trans hau
  have hsw := hsu.trans huw
  have hst := hsw.trans hwt
  filter_upwards [eventually_exp_power_gap hsw huw (ha.trans (hau.trans huw)) 1 (1/3) 2 1
      zero_lt_one (by norm_num),
    eventually_exp_power_gap hsa ha ha 1 (1/3) 2 0 zero_lt_one (by norm_num),
    eventually_exp_power_gap hst (huw.trans hwt) (lt_of_le_of_lt hs hst) 2 (1/3) 2 1
      (by norm_num) (by norm_num)] with N h1 h2 h3
  simp only [one_mul,zero_mul,zero_sub] at h1 h2 h3
  have hnon : 1 ≤ Real.exp ((N:ℝ)^u) := Real.one_le_exp (by positivity)
  have hlast : (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤
      2*Real.exp ((N:ℝ)^u-(N:ℝ)^t) := by
    rw [Real.exp_sub,div_eq_mul_inv,← Real.exp_neg]
    nlinarith only [hnon,Real.exp_pos (-((N:ℝ)^t))]
  have hlast' := hlast.trans h3
  have heq : -(2*(N:ℝ)^s) = -2*(N:ℝ)^s := by ring
  rw [heq] at h1 h2 hlast'
  linarith only [h1,h2,hlast']

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem solution {s a u w t : ℝ} (hs : 0 ≤ s) (hsa : s < a)
    (hau : a < u) (huw : u < w) (hwt : w < t) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) + Real.exp (-((N:ℝ)^a)) +
        (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤ Real.exp (-2*(N:ℝ)^s) := by
  first
    | exact OAI.QAC.eventually_backward_cost hs hsa hau huw hwt
    | exact OAI.QAC.eventually_backward_cost
    | (apply OAI.QAC.eventually_backward_cost <;> assumption)
    | (intros; apply OAI.QAC.eventually_backward_cost <;> assumption)
