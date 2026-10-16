-- Prove2me | solution 1 for OAI.Problem310.RoutingPath.noDefault_iff_exists_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:39:31.539656+00:00
-- url     : https://prove2.me/submissions/5a7ff3f6-488b-47e6-9831-f0422fba0c70

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean:L160-L191
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutingPath.noDefault_iff_exists_path. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_not_mem

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingPath ----
namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- A route with no default child is represented by a vector of nondefault
children. This is the deterministic event equality needed for path-cylinder
probability estimates. -/
theorem noDefault_iff_exists_path {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M,
        routeFrom choose d [] x = List.ofFn (fun i => (f i).castSucc) := by
  rw [noDefault_iff_not_mem]
  constructor
  · intro h
    let L := routeFrom choose d [] x
    have hL : L.length = d := by simp [L]
    have hentry : ∀ i : Fin d, L[i.val]'(by rw [hL]; exact i.isLt) ≠ Fin.last M := by
      intro i heq
      apply h
      rw [← heq]
      exact List.getElem_mem _
    let f : Fin d → Fin M := fun i =>
      (L[i.val]'(by rw [hL]; exact i.isLt)).castPred (hentry i)
    refine ⟨f, ?_⟩
    change L = _
    apply List.ext_getElem
    · simp [hL]
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      simp only [f, Fin.castSucc_castPred]
  · rintro ⟨f, hf⟩
    rw [hf]
    simp only [List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last (f i) hi

end Problem310.RoutingPath

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutingPath


theorem solution.{u_X} : type_of% @_root_.OAI.Problem310.RoutingPath.noDefault_iff_exists_path.{u_X} := @_root_.OAI.Problem310.RoutingPath.noDefault_iff_exists_path.{u_X}
