-- Prove2me | solution 1 for OAI.Solenoidal.mixedDerivative_eqOn_cell
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:27:53.494561+00:00
-- url     : https://prove2.me/submissions/e4ef6ec5-5a4d-4335-ba02-d0553e8e1a9b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/BoxJets.lean:L158-L175
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.mixedDerivative_eqOn_cell. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ScheduledForce ----
namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem mixedDerivative_contDiff {u : Field} (hu : Smooth u) (α : List (Fin 4)) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDerivative u α) := by
  induction α with
  | nil => exact hu
  | cons j α ih => exact directional_contDiff ih (spacetimeBasis j)

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.BoxJets ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! SheetFlows box jets. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

end BoxExpr

theorem mixedDerivative_eqOn_open {u v : Field} {S : Set SpaceTime} (hS : IsOpen S)
    (h : Set.EqOn (fun z => u z.1 z.2) (fun z => v z.1 z.2) S) (α : List (Fin 4)) :
    Set.EqOn (mixedDerivative u α) (mixedDerivative v α) S := by
  induction α with
  | nil => exact h
  | cons j α ih =>
      intro z hz
      change fderiv ℝ (mixedDerivative u α) z (spacetimeBasis j) = _
      rw [(ih.eventuallyEq_of_mem (hS.mem_nhds hz)).fderiv_eq]
      rfl

theorem mixedDerivative_eqOn_cell {u v : Field} (hu : Smooth u) (hv : Smooth v)
    (h : Set.EqOn (fun z => u z.1 z.2) (fun z => v z.1 z.2) closedPeriodCell)
    (α : List (Fin 4)) :
    Set.EqOn (mixedDerivative u α) (mixedDerivative v α) closedPeriodCell := by
  have hc : Convex ℝ closedPeriodCell := convex_Icc _ _
  have hn : (interior closedPeriodCell).Nonempty := by
    have he : interior closedPeriodCell =
        (Set.Ioo (0:ℝ) 1) ×ˢ (Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (0:ℝ) 10)) := by
      simp [closedPeriodCell, Set.Icc_prod_eq, interior_prod_eq, interior_Icc,
        ← Set.pi_univ_Icc, interior_pi_set]
    rw [he]
    exact ⟨(1/2,fun _ => 5), by norm_num [Set.mem_pi]⟩
  have hi : Set.EqOn (mixedDerivative u α) (mixedDerivative v α) (interior closedPeriodCell) :=
    mixedDerivative_eqOn_open isOpen_interior (h.mono interior_subset) α
  have hh := hi.closure (mixedDerivative_contDiff hu α).continuous (mixedDerivative_contDiff hv α).continuous
  have hclosure : closure (interior closedPeriodCell) = closedPeriodCell :=
    hc.closure_interior_eq_closure_of_nonempty_interior hn |>.trans isClosed_Icc.closure_eq
  rwa [hclosure] at hh

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.mixedDerivative_eqOn_cell := @_root_.OAI.Solenoidal.mixedDerivative_eqOn_cell
