-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.l2Energy_zero_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:25:07.492977+00:00
-- url     : https://prove2.me/submissions/01bd7b8c-996d-4c03-9eb1-4f761e79c25f

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal


theorem solution {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) (hc : Continuous v)
    (he : l2Energy V = 0) : v = 0 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ‖coordinateL2 i V‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp he
  have hi : ∀ i, ∀ᵐ x ∂(volume : Measure Space), (V : Space → Space) x i = 0 := by
    intro i
    have h0 : coordinateL2 i V = 0 := by
      have := hsq i (Finset.mem_univ i)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure Space))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) V
    have h2 : ((coordinateL2 i V : Lp ℝ 2 (volume : Measure Space)) : Space → ℝ) =ᵐ[volume] 0 := by
      rw [h0]; exact Lp.coeFn_zero _ _ _
    unfold coordinateL2 at h2
    filter_upwards [h1, h2] with x a b
    have := a.symm.trans b
    simpa using this
  have hall : ∀ᵐ x ∂(volume : Measure Space), ∀ i, (V : Space → Space) x i = 0 := ae_all_iff.mpr hi
  have hv0 : v =ᵐ[volume] (0 : Space → Space) := by
    filter_upwards [hv, hall] with x a b
    rw [← a]
    funext i
    exact b i
  exact (Continuous.ae_eq_iff_eq volume hc continuous_const).mp hv0

