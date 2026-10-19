-- Prove2me | solution 2 for OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:02:26.771316+00:00
-- url     : https://prove2.me/submissions/907d4a46-9a92-4269-9323-9afb3d3ea916

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean:L209-L230
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_KervaireHaarFlow_hasDerivAt_integral_compact

-- ---- from OAI.GroupTheory.Kervaire.HaarCurrents ----
namespace OAI

noncomputable section

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

namespace KervaireHaarFlow

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

/-- The infinitesimal form of invariance under a measure-preserving flow. -/
lemma integral_deriv_eq_zero_of_invariant {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t)
    (hinv : ∀ t, (∫ x, f t x ∂μ) = ∫ x, f 0 x ∂μ) (t : ℝ) :
    (∫ x, df t x ∂μ) = 0 := by
  have hfun : (fun u ↦ ∫ x, f u x ∂μ) = fun _ : ℝ ↦ ∫ x, f 0 x ∂μ := funext hinv
  have h := hasDerivAt_integral_compact (μ := μ) hf hd hfd t
  rw [hfun] at h
  exact h.unique (hasDerivAt_const t _)

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
-- [generator] trimmed: open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

end KervaireCurrentHomotopy

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI
variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

/-- Right-invariant vector fields on a compact unitary group have zero Haar divergence.
The derivative is the ambient Fréchet derivative. -/
lemma integral_unitary_fderiv_mul_eq_zero {g : B → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (x : B) ((x : B) * a) ∂μ) = 0 := by
  let h : ℝ → unitary B → B := fun t x ↦ (x : B) * exp (t • (a : B))
  have hh : Continuous (Function.uncurry h) := by
    exact (continuous_subtype_val.comp continuous_snd).mul
      ((exp_continuous).comp (continuous_fst.smul continuous_const))
  have hf : Continuous (Function.uncurry fun t x ↦ g (h t x)) := hg.continuous.comp hh
  have hd : Continuous (Function.uncurry fun t x ↦ fderiv ℝ g (h t x) (h t x * a)) :=
    ((hg.continuous_fderiv (by simp)).comp hh).clm_apply (hh.mul continuous_const)
  have hfd (t : ℝ) (x : unitary B) : HasDerivAt (fun u ↦ g (h u x))
      (fderiv ℝ g (h t x) (h t x * a)) t := by
    apply (hg.differentiable (by simp) (h t x)).hasFDerivAt.comp_hasDerivAt
    convert (hasDerivAt_const t (x : B)).mul
      (hasDerivAt_exp_smul_const (a : B) t) using 1 <;>
    first | rfl | simp [h, mul_assoc]
  have hinv (t : ℝ) : (∫ x, g (h t x) ∂μ) = ∫ x, g (h 0 x) ∂μ := by
    simpa [h, expFlow] using integral_mul_right_eq_self (μ := μ)
      (fun x : unitary B ↦ g (x : B)) (expFlow a t)
  simpa [h] using integral_deriv_eq_zero_of_invariant (μ := μ) hf hd hfd hinv 0

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireUnitaryHaarCurrent

namespace KervaireCompactUnitary
variable {B : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B]

end KervaireCompactUnitary

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireHaarFlow
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
open NormedSpace
open scoped ContDiff
attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI


theorem solution : type_of% @_root_.OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero := @_root_.OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero
