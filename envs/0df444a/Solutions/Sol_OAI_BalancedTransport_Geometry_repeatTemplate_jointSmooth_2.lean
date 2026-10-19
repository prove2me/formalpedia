-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.repeatTemplate_jointSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:08:39.147997+00:00
-- url     : https://prove2.me/submissions/9f86b675-bd82-49b7-b261-8dd27ef03c71

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Periodic.lean:L46-L61
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.repeatTemplate_jointSmooth. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Theorems.Thm_OAI_BalancedTransport_Geometry_repeatTemplate_eq

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set

lemma repeatTemplate_jointSmooth {v : Velocity} (hv : JointSmooth v) (hc : TimeCollars v) :
    JointSmooth (repeatTemplate v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let n : ℤ := ⌊z.1⌋
  have ht : z.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) := by
    have h₁ := Int.floor_le z.1
    have h₂ := Int.lt_floor_add_one z.1
    change -1 / 4 < z.1 - (⌊z.1⌋ : ℤ) ∧ z.1 - (⌊z.1⌋ : ℤ) < 5 / 4
    constructor <;> linarith
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × Space => v (y.1 - n) y.2) :=
    hv.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  apply hg.contDiffAt.congr_of_eventuallyEq
  have hnn : ∀ᶠ y : ℝ × Space in 𝓝 z, y.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) :=
    ((continuous_fst.sub continuous_const).continuousAt).eventually (isOpen_Ioo.mem_nhds ht)
  exact hnn.mono (fun y hy => repeatTemplate_eq hc hy y.2)

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.repeatTemplate_jointSmooth := @_root_.OAI.BalancedTransport.Geometry.repeatTemplate_jointSmooth
