-- Prove2me | solution 1 for OAI.KervaireUnitaryHaarCurrent.integral_liftField_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:20:21.499081+00:00
-- url     : https://prove2.me/submissions/1fd0d7b6-8f39-42f9-9bb1-304d0203eeb2

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents

open OAI OAI.KervaireUnitaryHaarCurrent
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open MeasureTheory VectorField
open scoped ContDiff
attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI

section
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]
theorem kh_deriv {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) (∫ x, df t x ∂μ) t := by
  have hcf : ∀ u, Continuous (f u) := fun u => hf.comp (continuous_const.prodMk continuous_id)
  have hcd : ∀ u, Continuous (df u) := fun u => hd.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ (X := S))).exists_bound_of_continuousOn
    hd.continuousOn
  have hint : Integrable (f t) μ := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := S)).exists_bound_of_continuousOn (hcf t).continuousOn
    exact Integrable.of_bound (hcf t).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => hC x trivial))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.closedBall t 1)
    (Metric.closedBall_mem_nhds t one_pos)
    (Filter.Eventually.of_forall (fun u => (hcf u).aestronglyMeasurable)) hint
    (hcd t).aestronglyMeasurable (bound := fun _ => M)
    (Filter.Eventually.of_forall (fun x u hu => hM (u, x) ⟨hu, trivial⟩)) (integrable_const M)
    (Filter.Eventually.of_forall (fun x u _ => hfd u x))).2


end


section
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]
variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]
theorem kh_zero {g : B → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (x : B) ((x : B) * a) ∂μ) = 0 := by
  have hsk : ∀ t : ℝ, t • (a : B) ∈ skewAdjoint B := fun t => (skewAdjoint.submodule ℝ B).smul_mem t a.2
  let u : ℝ → unitary B := fun t => ⟨NormedSpace.exp (t • (a : B)), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (hsk t)⟩
  have hu : ∀ t, ((u t : unitary B) : B) = NormedSpace.exp (t • (a : B)) := fun t => rfl
  let F : ℝ → unitary B → ℝ := fun t x => g ((x : B) * NormedSpace.exp (t • (a : B)))
  let dF : ℝ → unitary B → ℝ := fun t x =>
    fderiv ℝ g ((x : B) * NormedSpace.exp (t • (a : B))) ((x : B) * (NormedSpace.exp (t • (a : B)) * a))
  have hgd : ∀ y, HasFDerivAt g (fderiv ℝ g y) y := fun y => ((hg.differentiable (by simp)) y).hasFDerivAt
  have hpath : Continuous (fun p : ℝ × unitary B => (p.2 : B) * NormedSpace.exp (p.1 • (a : B))) := by
    have he : Continuous (fun t : ℝ => NormedSpace.exp (t • (a : B))) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact (continuous_subtype_val.comp continuous_snd).mul (he.comp continuous_fst)
  have hFc : Continuous (Function.uncurry F) := hg.continuous.comp hpath
  have hdFc : Continuous (Function.uncurry dF) := by
    have h1 : Continuous (fun p : ℝ × unitary B => fderiv ℝ g ((p.2 : B) * NormedSpace.exp (p.1 • (a : B)))) :=
      (hg.continuous_fderiv (by simp)).comp hpath
    have he : Continuous (fun t : ℝ => NormedSpace.exp (t • (a : B))) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have h2 : Continuous (fun p : ℝ × unitary B => (p.2 : B) * (NormedSpace.exp (p.1 • (a : B)) * a)) :=
      (continuous_subtype_val.comp continuous_snd).mul ((he.comp continuous_fst).mul continuous_const)
    exact h1.clm_apply h2
  have hFd : ∀ t x, HasDerivAt (fun s => F s x) (dF t x) t := by
    intro t x
    have h1 : HasDerivAt (fun s : ℝ => (x : B) * NormedSpace.exp (s • (a : B)))
        ((x : B) * (NormedSpace.exp (t • (a : B)) * a)) t :=
      (hasDerivAt_exp_smul_const (a : B) t).const_mul _
    exact (hgd _).comp_hasDerivAt t h1
  have hD := kh_deriv hFc hdFc hFd (μ := μ) 0
  have hconst : (fun s => ∫ x, F s x ∂μ) = fun _ => ∫ x, g (x : B) ∂μ := by
    funext s
    have := integral_mul_right_eq_self (μ := μ) (fun y : unitary B => g (y : B)) (u s)
    simpa [F, hu] using this
  rw [hconst] at hD
  have h0 := hD.unique (hasDerivAt_const (0 : ℝ) (∫ x, g (x : B) ∂μ))
  simpa [dF] using h0

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]
theorem solution (t : ℝ) {g : (ℝ × B) → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (t,(x : B)) (liftField (a : B) (t,(x : B))) ∂μ) = 0 := by
  have hg' : ContDiff ℝ ∞ (fun y : B => g (t, y)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have hfd : ∀ y : B, fderiv ℝ (fun y => g (t, y)) y =
      (fderiv ℝ g (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ B) := fun y =>
    (((hg.differentiable (by simp)) (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv
  have key := kh_zero (μ := μ) hg' a
  simp_rw [hfd] at key
  simpa [liftField_apply] using key
