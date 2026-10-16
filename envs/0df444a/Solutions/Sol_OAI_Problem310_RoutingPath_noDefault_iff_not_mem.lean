-- Prove2me | solution 1 for OAI.Problem310.RoutingPath.noDefault_iff_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:38:10.519312+00:00
-- url     : https://prove2.me/submissions/d678185a-7c35-4a42-b6f5-c0fa0fbc6219

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean:L140-L158
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutingPath.noDefault_iff_not_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Avoiding a default at every decision is the same as avoiding it in the
terminal path (for a route starting at the root). -/
theorem noDefault_iff_not_mem (choose : List ι → X → ι)
    (default : ι) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ default) ↔
      default ∉ routeFrom choose d [] x := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [routeFrom_succ, List.mem_append, List.mem_singleton, not_or]
      constructor
      · intro h
        refine ⟨ih.mp (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self d))), ?_⟩
        exact (h d (Nat.lt_succ_self d)).symm
      · rintro ⟨hprev, hlast⟩ k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkd | rfl
        · exact ih.mpr hprev k hkd
        · intro heq
          exact hlast heq.symm

end Problem310.RoutingPath

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutingPath


theorem solution.{u_ι,u_X} : type_of% @_root_.OAI.Problem310.RoutingPath.noDefault_iff_not_mem.{u_ι,u_X} := @_root_.OAI.Problem310.RoutingPath.noDefault_iff_not_mem.{u_ι,u_X}
