-- Prove2me | solution 2 for OAI.KervaireIncidenceCurrent.fderiv_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:11:13.071478+00:00
-- url     : https://prove2.me/submissions/82a96cc7-15af-4acd-b2e3-01ed84394c7a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean:L50-L91
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.fderiv_incidence. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent

-- ---- from OAI.GroupTheory.Kervaire.IncidenceTangent ----
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

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
/-- Its actual ambient Fréchet differential. -/
lemma fderiv_incidence {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (p v : ℝ × Alg K R) :
    fderiv ℝ (incidence f) p v =
      fderiv ℝ f (p.1,p.2.1) (v.1,v.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * v.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * in22 (star v.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star v.2.2.1 := by
  let cX : (ℝ × Alg K R) →L[ℝ] (ℝ × Mat K) :=
    (ContinuousLinearMap.fst ℝ ℝ (Alg K R)).prod
      ((ContinuousLinearMap.fst ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  let cQ : (ℝ × Alg K R) →L[ℝ] Mat (K ⊕ R) :=
    (ContinuousLinearMap.fst ℝ (Mat (K ⊕ R)) (Mat R)).comp
      ((ContinuousLinearMap.snd ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  let cT : (ℝ × Alg K R) →L[ℝ] Mat R :=
    (ContinuousLinearMap.snd ℝ (Mat (K ⊕ R)) (Mat R)).comp
      ((ContinuousLinearMap.snd ℝ (Mat K) (Mat (K ⊕ R) × Mat R)).comp
        (ContinuousLinearMap.snd ℝ ℝ (Alg K R)))
  have hX := (hf.differentiable (by simp) (cX p)).hasFDerivAt.comp p (cX.hasFDerivAt)
  have hS := (hasFDerivAt_const (𝕜 := ℝ) (in11 (K := K) (R := R) 1) p).add
    ((in22 (K := K) (R := R)).hasFDerivAt.comp p ((starL ℝ).hasFDerivAt.comp p cT.hasFDerivAt))
  have h1 : HasFDerivAt (fun z ↦ f (cX z) * cQ z) _ p := hX.mul' cQ.hasFDerivAt
  have h2 : HasFDerivAt (fun z ↦ f (cX z) * cQ z * (in11 (K := K) (R := R) 1 + in22 (star (cT z)))) _ p := h1.mul' hS
  have hd : HasFDerivAt (fun z ↦ f (cX z) * cQ z * (in11 (K := K) (R := R) 1 + in22 (star (cT z))) * star (cQ z)) _ p :=
    h2.mul' ((starL ℝ).hasFDerivAt.comp p cQ.hasFDerivAt)
  have heq : (fun x ↦ (f (cX x) * cQ x) * (in11 (K := K) (R := R) 1 + in22 (star (cT x))) * star (cQ x)) =
      incidence f := by
    funext x
    simp only [incidence, diag_eq_corner]
    rfl
  rw [heq] at hd
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    zero_add, ← diag_eq_corner, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    smul_eq_mul, Function.comp_apply]
  change f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star v.2.2.1 +
    (f (p.1,p.2.1) * p.2.2.1 * in22 (star v.2.2.2) +
      (f (p.1,p.2.1) * v.2.2.1 + fderiv ℝ f (p.1,p.2.1) (v.1,v.2.1) * p.2.2.1) *
        diag 1 (star p.2.2.2)) * star p.2.2.1 = _
  noncomm_ring

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireIncidenceCurrent
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


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.fderiv_incidence := @_root_.OAI.KervaireIncidenceCurrent.fderiv_incidence
