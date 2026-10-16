-- Prove2me | solution 1 for OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:43:50.232371+00:00
-- url     : https://prove2.me/submissions/cd015d0b-9a7d-4912-9686-a27d1f47f8f1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Computation.lean:L371-L384
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
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

theorem flatTerm_lipschitz (m : ℕ) : LipschitzWith (flatLipschitzBound m) (flatTerm m) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((contDiff_flatTerm m).differentiable (by simp))
  intro x
  rw [(hasDerivAt_flatTerm m x).deriv]
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, flatLipschitzBound,
    Nat.cast_add, Nat.cast_mul]
  calc
    |flatTerm (m + 2) x - (m : ℝ) * flatTerm (m + 1) x| ≤
        |flatTerm (m + 2) x| + |(m : ℝ) * flatTerm (m + 1) x| := abs_sub _ _
    _ ≤ (m + 2).factorial + (m : ℝ) * (m + 1).factorial := by
      simp only [abs_mul, Nat.abs_cast]
      
      gcongr <;> exact flatTerm_bound _ _

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


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz := @_root_.OAI.BoxTransport.Routing.Computation.flatTerm_lipschitz
