-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.SliceH2.sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:24:48.609923+00:00
-- url     : https://prove2.me/submissions/2916bd83-ecae-457c-b54d-34855f4691e0

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
theorem h44a_pd_sub {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) : pd j (fun x => f x - g x) = fun x => pd j f x - pd j g x := by
  funext x
  simp only [pd]
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

theorem h44a_pd_smooth {f : Space → Space} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (pd j f) := by
  have h := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h.clm_apply contDiff_const

theorem solution {u v : Space → Space} (hu : SliceH2 u) (hv : SliceH2 v) :
    SliceH2 (fun x => u x - v x) := by
  have du : Differentiable ℝ u := hu.smooth.differentiable (by simp)
  have dv : Differentiable ℝ v := hv.smooth.differentiable (by simp)
  have e1 := h44a_pd_sub du dv
  refine ⟨hu.smooth.sub hv.smooth, fun i => (hu.l2 i).sub (hv.l2 i), ?_, ?_⟩
  · intro i j
    rw [e1 j]
    exact (hu.d_l2 i j).sub (hv.d_l2 i j)
  · intro i j
    rw [e1 j]
    have d1 : Differentiable ℝ (pd j u) := (h44a_pd_smooth hu.smooth j).differentiable (by simp)
    have d2 : Differentiable ℝ (pd j v) := (h44a_pd_smooth hv.smooth j).differentiable (by simp)
    rw [h44a_pd_sub d1 d2 j]
    exact (hu.dd_l2 i j).sub (hv.dd_l2 i j)

