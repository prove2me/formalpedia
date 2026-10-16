-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.evalE_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:50:02.357363+00:00
-- url     : https://prove2.me/submissions/aafd38c5-0a5e-483b-9969-dc7b215b45fe

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Expressions.lean:L358-L408
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.evalE_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_flatTerm_lipschitz
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_qFlat_error
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_qGuardInv_error
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_value_bound

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

theorem mul_approx {x y a b ε B C A D : ℝ}
    (_hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hA : 0 ≤ A) (_hD : 0 ≤ D)
    (hx : |x| ≤ B) (hy : |y| ≤ C) (ha : |x - a| ≤ A * ε) (hb : |y - b| ≤ D * ε) :
    |x * y - a * b| ≤ ((B + A) * D + C * A) * ε := by
  have haa : |a| ≤ B + A := by
    calc
      |a| = |(a - x) + x| := by rw [sub_add_cancel]
      _ ≤ |a - x| + |x| := abs_add_le _ _
      _ ≤ A * ε + B := by rw [abs_sub_comm]; gcongr
      _ ≤ B + A := by nlinarith
  have hid : x * y - a * b = a * (y - b) + y * (x - a) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have hBn : 0 ≤ B + A := (abs_nonneg a).trans haa
  have hCn : 0 ≤ C := (abs_nonneg y).trans hy
  calc
    |a| * |y - b| + |y| * |x - a| ≤ (B + A) * (D * ε) + C * (A * ε) := by
      gcongr
    _ = _ := by ring

theorem evalE_error {e : Expr} (he : Valid e) (q : RationalPointCode) (N R : ℕ)
    (hR : ‖codeSpaceTime q‖ ≤ R) :
    |value e (codeSpaceTime q) - (Qval (evalE q N e) : ℝ)| ≤
      (ampE R e : ℝ) * ((N : ℝ) + 1)⁻¹ := by
  have hε : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by positivity
  have hε₁ : ((N : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  induction e with
  | zero => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | succ => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | left => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | right => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | pair e f ih₁ ih₂ =>
    simp only [value, evalE, Qval_add, Rat.cast_add, ampE, Nat.cast_add]
    have hee := ih₁ he.1
    have hff := ih₂ he.2
    have hid : value e (codeSpaceTime q) + value f (codeSpaceTime q) -
        ((Qval (evalE q N e) : ℝ) + (Qval (evalE q N f) : ℝ)) =
        (value e (codeSpaceTime q) - (Qval (evalE q N e) : ℝ)) +
        (value f (codeSpaceTime q) - (Qval (evalE q N f) : ℝ)) := by ring
    rw [hid, add_mul]
    exact (abs_add_le _ _).trans (add_le_add hee hff)
  | comp e f ih₁ ih₂ =>
    simp only [value, evalE, Qval_mul, Rat.cast_mul, ampE, Nat.cast_add, Nat.cast_mul]
    exact mul_approx hε hε₁ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (value_bound he.1 R hR) (value_bound he.2 R hR) (ih₁ he.1) (ih₂ he.2)
  | rfind' e ih => simpa only [value, evalE, Qval_neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm, ampE] using ih he
  | prec m e _ ih =>
    have hchild := ih he.1
    simp only [value, evalE, unaryValue, unaryEval, ampE, unaryAmp]
    split_ifs with h₀ h₁
    · simp
    · have hg := qGuardInv_error (Encodable.encode m / 3) (evalE q N e) (he.2 h₁ (codeSpaceTime q))
      apply hg.trans
      push_cast
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchild
        (by positivity : 0 ≤ 2 * ((Encodable.encode m / 3 : ℕ) + 1 : ℝ) ^ 2)
    · have hl := (flatTerm_lipschitz (Encodable.encode m / 3)).dist_le_mul
        (value e (codeSpaceTime q)) (Qval (evalE q N e))
      simp only [Real.dist_eq, NNReal.coe_natCast] at hl
      have ht := qFlat_error (Encodable.encode m / 3) (evalE q N e) N
      have hd := abs_sub_le (flatTerm (Encodable.encode m / 3) (value e (codeSpaceTime q)))
        (flatTerm (Encodable.encode m / 3) (Qval (evalE q N e)))
        (Qval (qFlat (Encodable.encode m / 3, evalE q N e, N)))
      apply hd.trans
      push_cast
      calc
        _ ≤ (flatLipschitzBound (Encodable.encode m / 3) : ℝ) *
            ((ampE R e : ℝ) * ((N : ℝ) + 1)⁻¹) + ((N : ℝ) + 1)⁻¹ := by
          gcongr
          exact hl.trans (mul_le_mul_of_nonneg_left hchild (Nat.cast_nonneg _))
        _ = _ := by ring

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


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.evalE_error := @_root_.OAI.BoxTransport.Routing.Computation.evalE_error
