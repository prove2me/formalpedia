-- Prove2me | solution 1 for OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:44:31.544483+00:00
-- url     : https://prove2.me/submissions/33937d96-f6e9-45cf-83da-bf5b16db5e44

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy

open OAI OAI.KervaireUnitaryHomotopy
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
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]
variable {B C}
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]


theorem solution {f g : ℝ × E → D}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t s : ℝ)
    (heq : ∀ x : unitary E, f (t,(x : E)) = g (s,(x : E)))
    (x : unitary E) (a : skewAdjoint.submodule ℝ E) :
    fderiv ℝ f (t,(x : E)) (0,(x : E)*(a : E)) =
      fderiv ℝ g (s,(x : E)) (0,(x : E)*(a : E)) := by
  let c : ℝ → E := fun τ => (x : E) * NormedSpace.exp (τ • (a : E))
  have hska : (a : E) ∈ skewAdjoint E := a.2
  have hc : ∀ τ, c τ ∈ unitary E := fun τ =>
    mul_mem x.2 (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem τ hska))
  have hc0 : c 0 = (x : E) := by simp [c]
  have hcd : HasDerivAt c ((x : E) * (a : E)) 0 := by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (a : E) 0).const_mul (x : E)
    simpa using this
  have hfun : (fun τ => f (t, c τ)) = fun τ => g (s, c τ) := by
    funext τ; exact heq ⟨c τ, hc τ⟩
  have h1 : HasDerivAt (fun τ => f (t, c τ)) (fderiv ℝ f (t, (x : E)) (0, (x : E) * (a : E))) 0 := by
    have hγ : HasDerivAt (fun τ => (t, c τ)) ((0 : ℝ), (x : E) * (a : E)) 0 :=
      (hasDerivAt_const 0 t).prodMk hcd
    have hfd := (hf.differentiable (by simp)).differentiableAt (x := (t, (x : E))) |>.hasFDerivAt
    exact hfd.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hγ (by simp [hc0])
  have h2 : HasDerivAt (fun τ => g (s, c τ)) (fderiv ℝ g (s, (x : E)) (0, (x : E) * (a : E))) 0 := by
    have hγ : HasDerivAt (fun τ => (s, c τ)) ((0 : ℝ), (x : E) * (a : E)) 0 :=
      (hasDerivAt_const 0 s).prodMk hcd
    have hgd := (hg.differentiable (by simp)).differentiableAt (x := (s, (x : E))) |>.hasFDerivAt
    exact hgd.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hγ (by simp [hc0])
  rw [hfun] at h1
  exact h1.unique h2

