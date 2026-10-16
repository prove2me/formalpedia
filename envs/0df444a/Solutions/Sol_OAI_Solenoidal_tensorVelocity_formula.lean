-- Prove2me | solution 1 for OAI.Solenoidal.tensorVelocity_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:31:23.789734+00:00
-- url     : https://prove2.me/submissions/10dccdd3-8e45-404e-aa63-69f641abbd4e

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/RationalFormula.lean:L125-L146
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.tensorVelocity_formula. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.SheetFlows.RationalFormula ----
namespace OAI

/-! SheetFlows rational formula. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

end BoxExpr

namespace HasRationalFormula

end HasRationalFormula

theorem tensorVelocity_formula (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (h : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    HasRationalFormula (tensorVelocity i g) := by
  classical
  let p := fun j => Classical.choice (h j)
  let e : BoxExpr := .mul (.mul (spatialCoordinate 0 (p 0).expression)
    (spatialCoordinate 1 (p 1).expression)) (spatialCoordinate 2 (p 2).expression)
  refine ⟨fun j => .mul e (.const (if j=i then 1 else 0)), ?_⟩
  intro z hz
  have hx (j : Fin 3) : z.2 j ∈ Set.Icc (0:ℝ) 10 := ⟨hz.1.2 j,hz.2.2 j⟩
  ext j
  have h₀ := (p 0).on_chart (hx 0)
  have h₁ := (p 1).on_chart (hx 1)
  have h₂ := (p 2).on_chart (hx 2)
  simp only [tensorVelocity,tensorScalar,Fin.prod_univ_succ,Fin.isValue,
    Fin.prod_univ_zero,mul_one,Pi.smul_apply,smul_eq_mul,
    expressionField,BoxExpr.eval,e,spatialCoordinate_eval]
  change g 0 (z.2 0) * (g 1 (z.2 1) * g 2 (z.2 2)) * basis i j = _
  rw [h₀,h₁,h₂]
  by_cases hji : j=i
  · subst j; simp [basis,mul_assoc]
  · simp [basis,hji]

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.tensorVelocity_formula := @_root_.OAI.Solenoidal.tensorVelocity_formula
