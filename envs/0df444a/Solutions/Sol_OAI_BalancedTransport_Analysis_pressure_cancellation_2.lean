-- Prove2me | solution 2 for OAI.BalancedTransport.Analysis.pressure_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:54:58.676144+00:00
-- url     : https://prove2.me/submissions/6532b964-fc5b-41e7-b558-c8558f991ceb

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Energy.lean:L117-L139
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.pressure_cancellation. The node keeps its source
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

theorem pd_apply (i j : Fin 3) {f : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => f y j) x = pd i f x j := by
  simp only [pd, fderiv_apply hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

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

lemma integral_mul_pd_eq_neg_pd_mul {f g : Space → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (hdg : Integrable (fun x => pd j f x * g x) (volume : Measure Space))
    (hfd : Integrable (fun x => f x * pd j g x) (volume : Measure Space))
    (hfg : Integrable (fun x => f x * g x) (volume : Measure Space)) :
    (∫ x, f x * pd j g x) = - ∫ x, pd j f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdg hfd hfg
    (fun x _ => hf x) (fun x _ => hg x)

theorem pressure_cancellation {w : Space → Space} {p : Space → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x, ∑ j, pd j w x j = 0)
    (hw₂ : ∀ j, MemLp (fun x => w x j) 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (fun x => pd j w x j) 2 (volume : Measure Space))
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hdp₂ : ∀ j, MemLp (pd j p) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, w x j * pd j p x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => w x j) x = pd j w x j :=
    pd_apply j j (hw.differentiable (by simp) x)
  have hdj (j : Fin 3) : Integrable (fun x => pd j w x j * p x) (volume : Measure Space) :=
    (hdw₂ j).integrable_mul hp₂
  have H (j : Fin 3) : (∫ x, w x j * pd j p x) = -∫ x, pd j w x j * p x := by
    have hdj' : Integrable (fun x => pd j (fun x => w x j) x * p x) (volume : Measure Space) := by
      simpa only [he] using hdj j
    simpa only [he] using integral_mul_pd_eq_neg_pd_mul
      ((contDiff_pi.mp hw j).differentiable (by simp)) (hp.differentiable (by simp)) j
      hdj' ((hw₂ j).integrable_mul (hdp₂ j)) ((hw₂ j).integrable_mul hp₂)
  simp only [H, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun j _ => hdj j)]
  have hz (x : Space) : (∑ j, pd j w x j * p x) = 0 := by
    rw [← Finset.sum_mul, hdiv x, zero_mul]
  simp only [hz, integral_zero, neg_zero]

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.pressure_cancellation := @_root_.OAI.BalancedTransport.Analysis.pressure_cancellation
