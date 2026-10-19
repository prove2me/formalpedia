-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.pressure_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:27:12.30448+00:00
-- url     : https://prove2.me/submissions/79072856-14e0-4c5f-acad-d0306152cea0

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem h44p_fderiv_comp {w : Space → Space} (hw : Differentiable ℝ w) (j : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => w y j) x v = fderiv ℝ w x v j := by
  have h := (hasFDerivAt_apply j (w x)).comp x (hw x).hasFDerivAt
  rw [show (fun y => w y j) = (fun f : Space => f j) ∘ w from rfl, h.fderiv]
  rfl

theorem solution {w : Space → Space} {p : Space → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x, ∑ j, pd j w x j = 0)
    (hw₂ : ∀ j, MemLp (fun x => w x j) 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (fun x => pd j w x j) 2 (volume : Measure Space))
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hdp₂ : ∀ j, MemLp (pd j p) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, w x j * pd j p x) = 0 := by
  have dw : Differentiable ℝ w := hw.differentiable (by simp)
  have dp : Differentiable ℝ p := hp.differentiable (by simp)
  have hI : ∀ j, Integrable (fun x => pd j w x j * p x) (volume : Measure Space) :=
    fun j => (hdw₂ j).integrable_mul hp₂
  have key : ∀ j, ∫ x, w x j * pd j p x = - ∫ x, pd j w x j * p x := by
    intro j
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (f := fun x => w x j) (g := p) (v := Pi.single j 1)
      ?_ ?_ ?_ (fun x _ => (show DifferentiableAt ℝ ((fun f : Space => f j) ∘ w) x from ((hasFDerivAt_apply j (w x)).comp x (dw x).hasFDerivAt).differentiableAt))
      (fun x _ => dp x)
    · simp only [h44p_fderiv_comp dw] at h
      exact h
    · simp only [h44p_fderiv_comp dw]; exact hI j
    · exact (hw₂ j).integrable_mul (hdp₂ j)
    · exact (hw₂ j).integrable_mul hp₂
  simp only [key]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hI j)]
  simp only [← Finset.sum_mul, hdiv, zero_mul, integral_zero, neg_zero]

