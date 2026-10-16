-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.qFlat_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:45:48.192529+00:00
-- url     : https://prove2.me/submissions/c66c1e1d-2093-4ae8-ba37-0e9491ac2bcd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Computation.lean:L425-L453
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.qFlat_error. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Computable rational arithmetic and exponential/flat-function approximation. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace BoxTransport.Routing.Computation

theorem real_exp_taylor_bound (x : ℝ) (n : ℕ) (h : |x| / (n + 1) ≤ 1 / 2) :
    |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤
      |x| ^ n / n.factorial * 2 := by
  have hc := Complex.exp_bound' (x := (x : ℂ)) (n := n) (by simpa [Real.norm_eq_abs] using h)
  rw [← Complex.ofReal_exp] at hc
  have he : (∑ m ∈ Finset.range n, (x : ℂ) ^ m / (m.factorial : ℂ)) =
      ((∑ m ∈ Finset.range n, x ^ m / m.factorial : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_sub, Complex.norm_real] at hc
  simpa [Real.norm_eq_abs] using hc

theorem qExp_error (q : QCode) (N : ℕ) :
    |Real.exp (Qval q) - (Qval (qExp (q, N)) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ := by
  have h := (expStop_iff q N (Nat.find (exists_expStop (q, N)))).1
    (Nat.find_spec (exists_expStop (q, N)))
  rw [qExp, Qval_taylor]
  push_cast
  exact (real_exp_taylor_bound _ _ h.1).trans h.2

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem flatTerm_zero {m : ℕ} {x : ℝ} (hx : x ≤ 0) : flatTerm m x = 0 := by
  simp [flatTerm, expNegInvGlue.zero_of_nonpos hx]

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem Qval_bound (q : QCode) : |Qval q| ≤ qBound q := by
  rw [Qval, abs_div, abs_of_pos (by positivity : (0 : ℚ) < q.2.2 + 1)]
  have h : |(q.1 : ℚ) - q.2.1| ≤ (q.1 : ℚ) + q.2.1 := by
    simpa only [Nat.abs_cast] using abs_sub (q.1 : ℚ) q.2.1
  apply le_trans (div_le_self (abs_nonneg _) (by norm_cast; omega))
  simpa [qBound] using h

theorem qFlat_error (m : ℕ) (q : QCode) (N : ℕ) :
    |flatTerm m (Qval q) - (Qval (qFlat (m, q, N)) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ := by
  by_cases hq : qLe q qZero
  · rw [qFlat, ite_eq_left hq, Qval_zero, Rat.cast_zero, sub_zero,
      flatTerm_zero (by exact_mod_cast (show Qval q ≤ 0 from by simpa using (qLe_iff q qZero).1 hq)), abs_zero]
    positivity
  have hp : (0 : ℝ) < Qval q := by
    exact_mod_cast lt_of_not_ge (by simpa only [qLe_iff, Qval_zero] using hq)
  let w := qPow (qInv q) m
  let B := qBound w
  have hB : |(Qval w : ℝ)| ≤ (B : ℝ) := by exact_mod_cast Qval_bound w
  have hw : (Qval w : ℝ) = (Qval q : ℝ)⁻¹ ^ m := by simp [w]
  have hx : (Qval (qNeg (qInv q)) : ℝ) = -(Qval q : ℝ)⁻¹ := by simp
  have he := qExp_error (qNeg (qInv q)) ((N + 1) * (B + 1))
  rw [hx] at he
  rw [qFlat, ite_eq_right hq]
  change |flatTerm m (Qval q) - (Qval (qMul w
    (qExp (qNeg (qInv q), (N + 1) * (B + 1)))) : ℝ)| ≤ _
  rw [Qval_mul, Rat.cast_mul]
  have ht : flatTerm m (Qval q) = (Qval w : ℝ) * Real.exp (-(Qval q : ℝ)⁻¹) := by
    simp only [flatTerm, expNegInvGlue, not_le.mpr hp, ↓reduceIte, hw]
  rw [ht, ← mul_sub, abs_mul]
  apply le_trans (mul_le_mul hB he (abs_nonneg _) (Nat.cast_nonneg B))
  push_cast
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have hn : (0 : ℝ) < N + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  field_simp
  nlinarith

end BoxTransport.Routing.Computation

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.qFlat_error := @_root_.OAI.BoxTransport.Routing.Computation.qFlat_error
