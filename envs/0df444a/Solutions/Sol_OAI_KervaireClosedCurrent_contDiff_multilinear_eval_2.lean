-- Prove2me | solution 2 for OAI.KervaireClosedCurrent.contDiff_multilinear_eval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:59:05.305801+00:00
-- url     : https://prove2.me/submissions/013e84d7-1f78-4481-b796-c3e9c3077099

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean:L78-L105
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireClosedCurrent.contDiff_multilinear_eval. The node keeps its source
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

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of simultaneous evaluation, including a varying multilinear map. -/
lemma contDiff_multilinear_eval {n : ℕ}
    {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ f) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ f x (V · x)) := by
  induction n with
  | zero =>
    let ev : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) F →L[ℝ] F :=
      { toFun := fun T ↦ T 0
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        cont := by fun_prop }
    convert ev.contDiff.comp hf using 1
    funext x
    exact congrArg (f x) (Subsingleton.elim _ _)
  | succ n ih =>
    have hc : ContDiff ℝ ∞ (fun x ↦ (f x).curryLeft (V 0 x)) :=
      by
        let L : ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) ↦ E) F ≃L[ℝ]
            E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F :=
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) ↦ E) F).toContinuousLinearEquiv
        exact (L.contDiff.comp hf).clm_apply (hV 0)
    convert ih hc (fun i ↦ hV i.succ) using 1
    funext x
    change f x (fun i ↦ V i x) = f x (Fin.cons (V 0 x) (fun i ↦ V i.succ x))
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
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
open OAI OAI.KervaireClosedCurrent
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


theorem solution : type_of% @_root_.OAI.KervaireClosedCurrent.contDiff_multilinear_eval := @_root_.OAI.KervaireClosedCurrent.contDiff_multilinear_eval
