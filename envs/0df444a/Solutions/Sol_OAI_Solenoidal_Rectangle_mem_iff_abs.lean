-- Prove2me | solution 1 for OAI.Solenoidal.Rectangle.mem_iff_abs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:13:21.519829+00:00
-- url     : https://prove2.me/submissions/67afac26-8cb1-4bec-98a8-756dabc719c7

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/RectangleGeometry.lean:L30-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.Rectangle.mem_iff_abs. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.SheetFlows.RectangleGeometry ----
namespace OAI

/-! SheetFlows rectangle geometry. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace Rectangle

theorem mem_iff_abs (R : Rectangle) (y : Plane) :
    y ∈ R.carrier ↔ ∀ j, |y j - R.center j| ≤ R.halfWidth j := by
  simp only [carrier, Set.mem_ofPred_eq, abs_le]
  constructor
  · intro h j
    have hl := (h j).1
    have hu := (h j).2
    dsimp [center, halfWidth]
    constructor <;> linarith
  · intro h j
    have hl := (h j).1
    have hu := (h j).2
    dsimp [center, halfWidth] at hl hu
    constructor <;> linarith

end Rectangle

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal OAI.Solenoidal.Rectangle
open Set MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Solenoidal.Rectangle.mem_iff_abs := @_root_.OAI.Solenoidal.Rectangle.mem_iff_abs
