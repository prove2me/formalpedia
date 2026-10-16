-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:48:27.306988+00:00
-- url     : https://prove2.me/submissions/b88ed003-ae0d-4a9a-a335-1d016e0fd9d2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Expressions.lean:L298-L321
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.value_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_flatTerm_bound

-- ---- from OAI.Analysis.BoxTransport.Computation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem Qval_bound (q : QCode) : |Qval q| ≤ qBound q := by
  rw [Qval, abs_div, abs_of_pos (by positivity : (0 : ℚ) < q.2.2 + 1)]
  have h : |(q.1 : ℚ) - q.2.1| ≤ (q.1 : ℚ) + q.2.1 := by
    simpa only [Nat.abs_cast] using abs_sub (q.1 : ℚ) q.2.1
  apply le_trans (div_le_self (abs_nonneg _) (by norm_cast; omega))
  simpa [qBound] using h

end BoxTransport.Routing.Computation

end

end OAI

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

theorem coord_le_norm (j : Axis) (p : SpaceTime) :
    |value (varE j) p| ≤ ‖p‖ := by
  cases j with
  | none => exact norm_fst_le p
  | some j =>
    simpa using (norm_le_pi_norm p.2 j).trans (norm_snd_le p)

theorem value_bound {e : Expr} (he : Valid e) (R : ℕ) {p : SpaceTime} (hp : ‖p‖ ≤ R) :
    |value e p| ≤ boundE R e := by
  induction e with
  | zero => exact (coord_le_norm none p).trans hp
  | succ => exact (coord_le_norm (some 0) p).trans hp
  | left => exact (coord_le_norm (some 1) p).trans hp
  | right => exact (coord_le_norm (some 2) p).trans hp
  | pair e f ih₁ ih₂ =>
    exact (abs_add_le _ _).trans (by exact_mod_cast add_le_add (ih₁ he.1) (ih₂ he.2))
  | comp e f ih₁ ih₂ =>
    simpa only [value, boundE, Nat.cast_mul, abs_mul] using
      mul_le_mul (ih₁ he.1) (ih₂ he.2) (abs_nonneg _) (Nat.cast_nonneg _)
  | rfind' e ih => simpa only [value, abs_neg, boundE] using ih he
  | prec m e _ ih =>
    simp only [value, unaryValue, boundE, unaryBound]
    split_ifs with h₀ h₁
    · exact_mod_cast Qval_bound (Denumerable.ofNat QCode (Encodable.encode m / 3))
    · have hb := he.2 h₁ p
      have hne := nonzero_of_inverse_bound hb
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hne)]
      have h := (inv_le_iff_one_le_mul₀ (by positivity : 0 < ((Encodable.encode m / 3 : ℕ) : ℝ) + 1)).mp hb
      push_cast
      nlinarith
    · exact flatTerm_bound _ _

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


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.value_bound := @_root_.OAI.BoxTransport.Routing.Computation.value_bound
