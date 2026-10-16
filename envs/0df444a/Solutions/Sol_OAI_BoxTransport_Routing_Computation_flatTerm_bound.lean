-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.flatTerm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:42:10.588723+00:00
-- url     : https://prove2.me/submissions/16665cae-fe24-46f9-ab78-2339af8eb322

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Computation.lean:L351-L367
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.flatTerm_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation

-- ---- from OAI.Analysis.BoxTransport.Computation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Computable rational arithmetic and exponential/flat-function approximation. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem flatTerm_zero {m : ℕ} {x : ℝ} (hx : x ≤ 0) : flatTerm m x = 0 := by
  simp [flatTerm, expNegInvGlue.zero_of_nonpos hx]

theorem flatTerm_nonneg (m : ℕ) (x : ℝ) : 0 ≤ flatTerm m x := by
  by_cases hx : x ≤ 0
  · rw [flatTerm_zero hx]
  · unfold flatTerm
    have : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_not_ge hx)
    exact mul_nonneg (pow_nonneg this _) (expNegInvGlue.nonneg x)

theorem flatTerm_bound (m : ℕ) (x : ℝ) : |flatTerm m x| ≤ (m.factorial : ℝ) := by
  rw [abs_of_nonneg (flatTerm_nonneg m x)]
  by_cases hx : x ≤ 0
  · rw [flatTerm_zero hx]
    positivity
  have hv : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr (lt_of_not_ge hx))
  have hterm : x⁻¹ ^ m / (m.factorial : ℝ) ≤ Real.exp x⁻¹ := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg hv (m + 1))
    exact Finset.single_le_sum (f := fun i : ℕ => x⁻¹ ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hm).mp hterm)
    (Real.exp_pos (-x⁻¹)).le
  have he : Real.exp x⁻¹ * Real.exp (-x⁻¹) = 1 := by rw [← Real.exp_add]; simp
  unfold flatTerm expNegInvGlue
  rw [ite_eq_right hx]
  nlinarith [he]

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.flatTerm_bound := @_root_.OAI.BoxTransport.Routing.Computation.flatTerm_bound
