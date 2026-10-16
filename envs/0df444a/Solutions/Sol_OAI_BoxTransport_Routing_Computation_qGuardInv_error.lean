-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.qGuardInv_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:47:03.324798+00:00
-- url     : https://prove2.me/submissions/85ba5ba1-25cc-4b17-9c8d-be7a6d7b0932

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Expressions.lean:L221-L266
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.qGuardInv_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions

-- ---- from OAI.Analysis.BoxTransport.Expressions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Smooth expression calculus and effective mixed derivatives. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

theorem qGuardInv_error (b : ℕ) (q : QCode) {x : ℝ}
    (hx : ((b : ℝ) + 1)⁻¹ ≤ |x|) :
    |x⁻¹ - (Qval (qGuardInv b q) : ℝ)| ≤ 2 * ((b : ℝ) + 1) ^ 2 * |x - (Qval q : ℝ)| := by
  let D : ℝ := (b : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hx0 := nonzero_of_inverse_bound hx
  have hxmul : 1 ≤ |x| * D := (inv_le_iff_one_le_mul₀ hD).mp hx
  have hinvx : |x⁻¹| ≤ D := by
    rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hx0)]
    nlinarith
  unfold qGuardInv
  split_ifs with hq
  · have hq' : (2 * D)⁻¹ ≤ |(Qval q : ℝ)| := by
      have h := (qLe_iff _ _).1 hq
      simp only [Qval_inv, Qval_nat, Qval_abs] at h
      have hc := (Rat.cast_le (K := ℝ)).2 h
      simpa [D] using hc
    have hq0 : (Qval q : ℝ) ≠ 0 := abs_pos.mp ((by positivity : (0 : ℝ) < (2 * D)⁻¹).trans_le hq')
    have hinvq : |(Qval q : ℝ)⁻¹| ≤ 2 * D := by
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hq0)]
      have h := (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2 * D)).mp hq'
      nlinarith
    simp only [Qval_inv, Rat.cast_inv]
    have hi : x⁻¹ - (Qval q : ℝ)⁻¹ = x⁻¹ * (Qval q : ℝ)⁻¹ * ((Qval q : ℝ) - x) := by
      field_simp
    rw [hi, abs_mul, abs_mul, abs_sub_comm (Qval q : ℝ) x]
    calc
      |x⁻¹| * |(Qval q : ℝ)⁻¹| * |x - (Qval q : ℝ)| ≤ D * (2 * D) * |x - (Qval q : ℝ)| := by
        gcongr
      _ = _ := by dsimp [D]; ring
  · have hq' : |(Qval q : ℝ)| < (2 * D)⁻¹ := by
      have h := lt_of_not_ge ((qLe_iff _ _).not.mp hq)
      simp only [Qval_inv, Qval_nat, Qval_abs] at h
      have hc := (Rat.cast_lt (K := ℝ)).2 h
      simpa [D] using hc
    have hdist : (2 * D)⁻¹ ≤ |x - (Qval q : ℝ)| := by
      have ht := abs_add_le (x - (Qval q : ℝ)) (Qval q : ℝ)
      have hid : (2 * D)⁻¹ + (2 * D)⁻¹ = D⁻¹ := by field_simp; ring
      dsimp [D] at hx ⊢ hq' hid
      rw [sub_add_cancel] at ht
      linarith
    simp only [Qval_zero, Rat.cast_zero, sub_zero]
    have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2 * D ^ 2)
    have hid : 2 * D ^ 2 * (2 * D)⁻¹ = D := by field_simp
    rw [hid] at hmul
    exact hinvx.trans hmul

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Primrec Computable
attribute [fun_prop] Primrec.const Primrec.id Primrec.fst Primrec.snd Primrec.comp Primrec.pair Primrec.succ Primrec.encode Primrec.ofNat
attribute [fun_prop] Computable.const Computable.id Computable.fst Computable.snd Computable.comp Computable.pair

attribute [fun_prop] Code.primrec_rfind' primrec_qNat primrec_qBound primrec_qInv primrec_qAbs primrec_qNeg primrec_factorial

attribute [fun_prop] Primrec.to_comp computable_qFlat

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Representable

namespace Representable

end Representable

end BoxTransport.Routing.Computation

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.qGuardInv_error := @_root_.OAI.BoxTransport.Routing.Computation.qGuardInv_error
