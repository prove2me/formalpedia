-- Prove2me | solution 1 for OAI.Solenoidal.norm_flatten
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:46:37.842965+00:00
-- url     : https://prove2.me/submissions/ebc74aba-6b93-494c-a536-b0ec2a96da7b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean:L287-L303
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.norm_flatten. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms

-- ---- from OAI.MathematicalPhysics.SheetFlows.CircuitPrograms ----
namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

namespace Circuit

end Circuit

namespace Computing

end Computing

theorem norm_flatten (z : SpaceTime) : ‖flatten z‖ = ‖z‖ := by
  rw [Prod.norm_def]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg z.1) (le_max_left _ _))).mpr
    intro j
    fin_cases j
    · exact le_max_left _ _
    all_goals exact (norm_le_pi_norm z.2 _).trans (le_max_right _ _)
  · apply max_le
    · exact norm_le_pi_norm (flatten z) 0
    · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
      intro j
      exact (show ‖z.2 j‖ ≤ ‖flatten z‖ by
        fin_cases j
        · exact norm_le_pi_norm (flatten z) 1
        · exact norm_le_pi_norm (flatten z) 2
        · exact norm_le_pi_norm (flatten z) 3)

namespace Computing

end Computing
end Solenoidal

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set Filter Encodable
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.norm_flatten := @_root_.OAI.Solenoidal.norm_flatten
