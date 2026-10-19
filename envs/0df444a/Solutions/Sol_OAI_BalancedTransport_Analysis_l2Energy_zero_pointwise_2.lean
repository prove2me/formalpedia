-- Prove2me | solution 2 for OAI.BalancedTransport.Analysis.l2Energy_zero_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:50:52.89343+00:00
-- url     : https://prove2.me/submissions/62934d96-5c7f-4b4c-ab0e-c4ec6c64be39

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergyCurve.lean:L86-L99
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.l2Energy_zero_pointwise. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EnergyCurve ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

lemma coordinateL2_coe (i : Fin 3) (V : Lp Space 2 (volume : Measure Space)) :
    (coordinateL2 i V : Space → ℝ) =ᵐ[volume] fun x => (V : Space → Space) x i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma l2Energy_zero_pointwise {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) (hc : Continuous v)
    (he : l2Energy V = 0) : v = 0 := by
  have hz (i : Fin 3) : coordinateL2 i V = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖coordinateL2 j V‖)).mp he i (Finset.mem_univ _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  ext x i
  have hae : (fun x => v x i) =ᵐ[volume] (0 : Space → ℝ) := by
    filter_upwards [coordinateL2_coe i V, hv, Lp.coeFn_zero ℝ 2 (volume : Measure Space)] with x h₁ h₂ h₃
    rw [hz, h₃, h₂] at h₁
    exact h₁.symm
  have hi := ((Continuous.ae_eq_iff_eq volume ((continuous_apply i).comp hc) continuous_const).mp hae)
  exact congrFun hi x

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.l2Energy_zero_pointwise := @_root_.OAI.BalancedTransport.Analysis.l2Energy_zero_pointwise
