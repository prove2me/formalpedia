-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.transport_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:27:41.934611+00:00
-- url     : https://prove2.me/submissions/14f3ffff-8b16-4681-91db-88862cff00c1

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


theorem solution {v : Space → Space} {w : Space → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {C : ℝ} (hb : ∀ x, ‖v x‖ ≤ C) (hdb : ∀ x j, ‖pd j v x‖ ≤ C)
    (hdiv : ∀ x, ∑ j, pd j v x j = 0)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (pd j w) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, v x j * pd j w x * w x) = 0 := by
  simp only [pd] at hdiv hdb hdw₂ ⊢
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have dw : Differentiable ℝ w := hw.differentiable (by simp)
  have hvj : ∀ j, ∀ x, ‖v x j‖ ≤ C := fun j x => (norm_le_pi_norm (v x) j).trans (hb x)
  have hdvj : ∀ j x, ‖fderiv ℝ v x (Pi.single j 1) j‖ ≤ C :=
    fun j x => (norm_le_pi_norm (fderiv ℝ v x (Pi.single j 1)) j).trans (hdb x j)
  have mvj : ∀ j, AEStronglyMeasurable (fun x => v x j) (volume : Measure Space) :=
    fun j => ((continuous_apply j).comp hv.continuous).aestronglyMeasurable
  have mdvj : ∀ j, AEStronglyMeasurable (fun x => fderiv ℝ v x (Pi.single j 1) j)
      (volume : Measure Space) := by
    intro j
    have hc : Continuous (fun x => fderiv ℝ v x) := hv.continuous_fderiv (by simp)
    exact ((continuous_apply j).comp (hc.clm_apply continuous_const)).aestronglyMeasurable
  have hww : Integrable (fun x => w x * w x) (volume : Measure Space) := hw₂.integrable_mul hw₂
  have hdww : ∀ j, Integrable (fun x => fderiv ℝ w x (Pi.single j 1) * w x)
      (volume : Measure Space) := fun j => (hdw₂ j).integrable_mul hw₂
  have I1 : ∀ j, Integrable (fun x => fderiv ℝ v x (Pi.single j 1) j * (w x * w x))
      (volume : Measure Space) := fun j => hww.bdd_mul (mdvj j) (ae_of_all _ (hdvj j))
  have I2 : ∀ j, Integrable (fun x => v x j * fderiv ℝ w x (Pi.single j 1) * w x)
      (volume : Measure Space) := by
    intro j
    simpa only [mul_assoc] using (hdww j).bdd_mul (mvj j) (ae_of_all _ (hvj j))
  have key : ∀ j, 2 * ∫ x, v x j * fderiv ℝ w x (Pi.single j 1) * w x =
      - ∫ x, fderiv ℝ v x (Pi.single j 1) j * (w x * w x) := by
    intro j
    have hd : ∀ x, fderiv ℝ (fun y => v y j * w y) x (Pi.single j 1) =
        fderiv ℝ v x (Pi.single j 1) j * w x + v x j * fderiv ℝ w x (Pi.single j 1) := by
      intro x
      have h1 := ((hasFDerivAt_apply j (v x)).comp x (dv x).hasFDerivAt).mul (dw x).hasFDerivAt
      rw [show (fun y => v y j * w y) = ((fun f : Space => f j) ∘ v * w) from rfl, h1.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        Function.comp_apply]
      ring
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (f := fun y => v y j * w y) (g := w) (v := Pi.single j 1)
      (by simp only [hd]; exact ((I1 j).add (I2 j)).congr (ae_of_all _ (fun x => by (try simp only [Pi.add_apply]); ring)))
      ((I2 j).congr (ae_of_all _ (fun x => by (try simp only [Pi.add_apply]); ring)))
      ((hww.bdd_mul (mvj j) (ae_of_all _ (hvj j))).congr (ae_of_all _ (fun x => by (try simp only [Pi.add_apply]); ring)))
      (fun x _ => (show DifferentiableAt ℝ ((fun f : Space => f j) ∘ v) x from ((hasFDerivAt_apply j (v x)).comp x (dv x).hasFDerivAt).differentiableAt).mul (dw x))
      (fun x _ => dw x)
    simp only [hd] at h
    have e1 : ∫ x, v x j * w x * fderiv ℝ w x (Pi.single j 1) =
        ∫ x, v x j * fderiv ℝ w x (Pi.single j 1) * w x :=
      integral_congr_ae (ae_of_all _ (fun x => by (try simp only [Pi.add_apply]); ring))
    have e2 : ∫ x, (fderiv ℝ v x (Pi.single j 1) j * w x + v x j * fderiv ℝ w x (Pi.single j 1)) * w x
        = (∫ x, fderiv ℝ v x (Pi.single j 1) j * (w x * w x)) +
          ∫ x, v x j * fderiv ℝ w x (Pi.single j 1) * w x := by
      rw [← integral_add (I1 j) (I2 j)]
      exact integral_congr_ae (ae_of_all _ (fun x => by (try simp only [Pi.add_apply]); ring))
    rw [e1, e2] at h
    linarith
  have hsum : ∑ j, ∫ x, fderiv ℝ v x (Pi.single j 1) j * (w x * w x) = 0 := by
    rw [← integral_finsetSum _ (fun j _ => I1 j)]
    simp only [← Finset.sum_mul, hdiv, zero_mul, integral_zero]
  have hj : ∀ j, ∫ x, v x j * fderiv ℝ w x (Pi.single j 1) * w x =
      -(1/2) * ∫ x, fderiv ℝ v x (Pi.single j 1) j * (w x * w x) := by
    intro j; linarith [key j]
  rw [Finset.sum_congr rfl (fun j _ => hj j), ← Finset.mul_sum, hsum, mul_zero]

