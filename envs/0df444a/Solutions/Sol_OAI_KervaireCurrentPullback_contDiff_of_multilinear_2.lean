-- Prove2me | solution 2 for OAI.KervaireCurrentPullback.contDiff_of_multilinear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:06:01.413501+00:00
-- url     : https://prove2.me/submissions/82aa24b1-6ba8-46ef-899f-64682c964eda

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean:L30-L46
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireCurrentPullback.contDiff_of_multilinear. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.CurrentPullback ----
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

namespace KervaireCurrentPullback

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The finite-dimensional alternating-map subspace is split by a continuous linear map.
This lets ordinary multilinear calculus establish smooth pullback without a manifold API. -/
lemma contDiff_of_multilinear {n : ℕ} [FiniteDimensional ℝ F] [FiniteDimensional ℝ H]
    {f : E → F [⋀^Fin n]→L[ℝ] H}
    (hf : ContDiff ℝ ∞ (fun x ↦ (f x).toContinuousMultilinearMap)) :
    ContDiff ℝ ∞ f := by
  let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ F) H) :=
    FiniteDimensional.of_injective ((ContinuousMultilinearMap.toMultilinearMapLinear : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ F) H →ₗ[ℝ] _))
      ContinuousMultilinearMap.toMultilinearMap_injective
  let L : (F [⋀^Fin n]→L[ℝ] H) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ F) H := toContinuousMultilinearMapCLM ℝ
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr toContinuousMultilinearMap_injective)
  let R' := R.toContinuousLinearMap
  convert R'.contDiff.comp hf using 1
  funext x
  exact (DFunLike.congr_fun hR (f x)).symm

end KervaireCurrentPullback

open MeasureTheory NormedSpace
open scoped ContDiff

namespace KervaireUnitaryTangent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

end KervaireUnitaryTangent

open Module Set ContinuousAlternatingMap
namespace KervaireAlternatingSpan
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireAlternatingSpan

namespace KervaireHorizontalCurrent
open MeasureTheory ContinuousAlternatingMap VectorField
open KervaireUnitaryHaarCurrent KervaireUnitaryTangent KervaireCurrentPullback
open scoped ContDiff
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompactSpace (unitary B)] [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

attribute [local instance] OAI.KervaireHorizontalCurrent.instNormedAlgebraRat_oAI
end KervaireHorizontalCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireCurrentPullback
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


theorem solution : type_of% @_root_.OAI.KervaireCurrentPullback.contDiff_of_multilinear := @_root_.OAI.KervaireCurrentPullback.contDiff_of_multilinear
