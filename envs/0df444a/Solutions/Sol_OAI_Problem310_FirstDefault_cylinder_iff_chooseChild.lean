-- Prove2me | solution 1 for OAI.Problem310.FirstDefault.cylinder_iff_chooseChild
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:03:50.033923+00:00
-- url     : https://prove2.me/submissions/eb98389f-5cc1-428a-8785-e8b280347b4a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefaultSelection.lean:L13-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FirstDefault.cylinder_iff_chooseChild. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Theorems.Thm_OAI_Problem310_OrderedRouting_chooseChild_eq_nondefault_iff

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FirstDefaultSelection ----
namespace OAI

universe u_Ω u_ι u_X u_Y

noncomputable section

namespace Problem310.FirstDefault

/-- A path cylinder is exactly the event that first-success routing selects
its prescribed child at each of its prescribed nodes. -/
theorem cylinder_iff_chooseChild {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f : Path M d) (ω : Ω) :
    ω ∈ cylinder S f ↔ ∀ k : Fin d,
      OrderedRouting.chooseChild (fun j => S (pathPrefix f k, j) ω) = (f k).castSucc := by
  constructor
  · intro h k
    apply (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mpr
    constructor
    · have hi := h ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
      simpa only [address, requiredBit, decide_true] using hi
    · intro j hj
      have hi := h ⟨k, ⟨j.val, lt_trans hj (Nat.lt_succ_self _)⟩⟩
      have hne : j.val ≠ (f k).val := Nat.ne_of_lt hj
      simpa only [address, requiredBit, hne, decide_false] using hi
  · intro h i
    obtain ⟨k, j⟩ := i
    obtain ⟨hsuccess, hprev⟩ :=
      (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mp (h k)
    by_cases heq : j.val = (f k).val
    · have ha : address f ⟨k, j⟩ = (pathPrefix f k, f k) := by
        apply Prod.ext
        · rfl
        · exact Fin.ext heq
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [ha, requiredBit, heq, decide_true] using hsuccess
    · have hlt : j.val < (f k).val := by omega
      have hj := hprev ⟨j.val, lt_trans hlt (f k).isLt⟩ hlt
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [address, requiredBit, heq, decide_false] using hj

end Problem310.FirstDefault

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FirstDefault


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.FirstDefault.cylinder_iff_chooseChild.{u_Ω} := @_root_.OAI.Problem310.FirstDefault.cylinder_iff_chooseChild.{u_Ω}
