-- Prove2me | solution 2 for OAI.BalancedTransport.Analysis.transport_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:52:54.524698+00:00
-- url     : https://prove2.me/submissions/0c637c09-7bbc-47c4-b235-4b2c2d5216cc

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Energy.lean:L82-L106
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.transport_cancellation. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pd_mul (i : Fin 3) {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = f x * pd i g x + g x * pd i f x := by
  simp only [pd, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

theorem pd_apply (i j : Fin 3) {f : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => f y j) x = pd i f x j := by
  simp only [pd, fderiv_apply hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Energy ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma integrable_bounded_mul_l2_mul_l2 {a f g : Space → ℝ} {C : ℝ}
    (ha : Continuous a) (hab : ∀ x, ‖a x‖ ≤ C)
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 (volume : Measure Space)) :
    Integrable (fun x => a x * f x * g x) (volume : Measure Space) := by
  convert (hf.integrable_mul hg).bdd_mul ha.aestronglyMeasurable
      (Eventually.of_forall hab) using 1
  ext x
  simp only [Pi.mul_apply, mul_assoc]

lemma integral_mul_pd_eq_neg_pd_mul {f g : Space → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (hdg : Integrable (fun x => pd j f x * g x) (volume : Measure Space))
    (hfd : Integrable (fun x => f x * pd j g x) (volume : Measure Space))
    (hfg : Integrable (fun x => f x * g x) (volume : Measure Space)) :
    (∫ x, f x * pd j g x) = - ∫ x, pd j f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdg hfd hfg
    (fun x _ => hf x) (fun x _ => hg x)

lemma transport_component {a w : Space → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (j : Fin 3) {C : ℝ} (hc : ∀ x, ‖a x‖ ≤ C) (hd : ∀ x, ‖pd j a x‖ ≤ C)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : MemLp (pd j w) 2 (volume : Measure Space)) :
    2 * (∫ x, a x * pd j w x * w x) = - ∫ x, pd j a x * w x * w x := by
  have Hi := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hdw₂ hw₂
  have Hj := integrable_bounded_mul_l2_mul_l2 (pd_contDiff j ha).continuous hd hw₂ hw₂
  have Hk := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hw₂ hw₂
  have he (x : Space) : pd j (fun x => w x * w x) x = 2 * (pd j w x * w x) := by
    rw [pd_mul j (hw.differentiable (by simp) x) (hw.differentiable (by simp) x)]
    ring
  have hdg : Integrable (fun x => pd j a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hj
  have hfg : Integrable (fun x => a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hk
  have hfd : Integrable (fun x => a x * pd j (fun x => w x * w x) x)
      (volume : Measure Space) := by
    convert Hi.const_mul 2 using 1
    ext x
    rw [he]
    ring
  have H := integral_mul_pd_eq_neg_pd_mul (ha.differentiable (by simp))
    ((hw.mul hw).differentiable (by simp)) j hdg hfd hfg
  have he' : (fun x => a x * pd j (fun x => w x * w x) x) =
      (fun x => 2 * (a x * pd j w x * w x)) := by
    ext x
    rw [he]
    ring
  rw [he', integral_const_mul] at H
  simpa only [mul_assoc] using H

theorem transport_cancellation {v : Space → Space} {w : Space → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {C : ℝ} (hb : ∀ x, ‖v x‖ ≤ C) (hdb : ∀ x j, ‖pd j v x‖ ≤ C)
    (hdiv : ∀ x, ∑ j, pd j v x j = 0)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (pd j w) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, v x j * pd j w x * w x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => v x j) x = pd j v x j :=
    pd_apply j j (hv.differentiable (by simp) x)
  have H (j : Fin 3) := transport_component (contDiff_pi.mp hv j) hw j
    (fun x => (norm_le_pi_norm (v x) j).trans (hb x))
    (fun x => by rw [he]; exact (norm_le_pi_norm (pd j v x) j).trans (hdb x j))
    hw₂ (hdw₂ j)
  have hdj (j : Fin 3) : Integrable (fun x => pd j v x j * w x * w x) (volume : Measure Space) := by
    apply integrable_bounded_mul_l2_mul_l2
      ((continuous_apply j).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) j).trans (hdb x j)) hw₂ hw₂
  have hsum : (∑ j, ∫ x, pd j v x j * w x * w x) = 0 := by
    rw [← integral_finsetSum _ (fun j _ => hdj j)]
    have hz (x : Space) : (∑ j, pd j v x j * w x * w x) = 0 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hdiv x, zero_mul, zero_mul]
    simp only [hz, integral_zero]
  have Hsum := congrArg (fun f : Fin 3 → ℝ => ∑ j, f j) (funext H)
  simp only [he, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, neg_zero] at Hsum
  linarith

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.transport_cancellation := @_root_.OAI.BalancedTransport.Analysis.transport_cancellation
