-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.exists_lifted_linear_filling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:23:30.717175+00:00
-- url     : https://prove2.me/submissions/0dce2496-8b1d-4579-95e7-734395fb1eff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean:L311-L332
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.exists_lifted_linear_filling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Theorems.Thm_OAI_Release075_MarkedLineData_reduced_linear_active_bound
import Theorems.Thm_OAI_Release075_TriangleFilling_Dipole_cancel

-- ---- from OAI.GroupTheory.Hyperbolic.Dipoles ----
namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Minimizing active size, not an assumed reduced-diagram axiom, produces a
filling with no cancellable adjacent labelled pair. -/
theorem exists_noDipole {w : List E} (h : Fillable flip color face w) :
    ∃ D : TriangleFilling flip color face w, IsEmpty D.Dipole := by
  have hex : ∃ n : ℕ, ∃ D : TriangleFilling flip color face w, D.activeCount = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.activeCount,D,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,⟨fun P => ?_⟩⟩
  obtain ⟨D',hless⟩ := P.cancel
  have hmin := Nat.find_min' hex (show ∃ A : TriangleFilling flip color face w,
      A.activeCount = D'.activeCount from ⟨D',rfl⟩)
  omega

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

end CyclicLink
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.LiftedFilling ----
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

theorem noDipole_forgetLift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

theorem exists_lifted_linear_filling (hf : Fillable (d.presentation hr).liftedFlip
    (d.presentation hr).liftedTarget (d.presentation hr).LiftedFace w) :
    ∃ D : TriangleFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w, D.activeCount ≤ 19*w.length := by
  classical
  by_cases hw : w = []
  · subst w
    refine ⟨TriangleFilling.empty,?_⟩
    unfold TriangleFilling.activeCount
    apply (Finset.card_le_univ _).trans
    change 0 ≤ _
    exact Nat.zero_le _
  · obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
    have hn : D.boundary ≠ [] := by
      intro he
      apply hw
      rw [← D.boundary_word,he,List.map_nil]
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
    have hbound := d.reduced_linear_active_bound hr D.forgetLift b hb
      (TriangleFilling.noDipole_forgetLift hD)
    rw [TriangleFilling.forgetLift_activeCount,List.length_map] at hbound
    exact ⟨D,by omega⟩

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.exists_lifted_linear_filling := @_root_.OAI.Release075.MarkedLineData.exists_lifted_linear_filling
