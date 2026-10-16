-- Prove2me | solution 1 for OAI.Problem310.RoutingPath.noDefault_iff_exists_choices
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:41:53.662103+00:00
-- url     : https://prove2.me/submissions/17631d95-6b4f-4389-bbce-084e42a5a933

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean:L193-L212
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutingPath.noDefault_iff_exists_choices. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_exists_path
import Theorems.Thm_OAI_Problem310_RoutingPath_routeFrom_eq_iff_choices

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- The no-default event is a union of the prescribed nondefault path cylinders. -/
theorem noDefault_iff_exists_choices {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M, ∀ (k : ℕ) (hk : k < d),
        choose ((List.ofFn (fun i => (f i).castSucc)).take k) x =
          (f ⟨k, hk⟩).castSucc := by
  rw [noDefault_iff_exists_path]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mp (by simpa using hf)
    simpa only [List.length_ofFn, List.getElem_ofFn] using hc
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mpr (by
        simpa only [List.length_ofFn, List.getElem_ofFn] using hf)
    simpa only [List.length_ofFn] using hc

end Problem310.RoutingPath

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutingPath


theorem solution.{u_X} : type_of% @_root_.OAI.Problem310.RoutingPath.noDefault_iff_exists_choices.{u_X} := @_root_.OAI.Problem310.RoutingPath.noDefault_iff_exists_choices.{u_X}
