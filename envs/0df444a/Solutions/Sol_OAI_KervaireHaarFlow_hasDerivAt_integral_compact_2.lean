-- Prove2me | solution 2 for OAI.KervaireHaarFlow.hasDerivAt_integral_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:57:34.760848+00:00
-- url     : https://prove2.me/submissions/65682656-ef85-4846-b351-e0ff47a540e3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean:L35-L55
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireHaarFlow.hasDerivAt_integral_compact. The node keeps its source
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

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma hasCompactSupport_of_compact (f : S → E) : HasCompactSupport f :=
  (isClosed_closure : IsClosed (tsupport f)).isCompact

omit [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma continuous_integrable {f : S → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (hasCompactSupport_of_compact f)

/-- Compactness supplies the domination needed for differentiation with respect to a real
parameter. This lemma only assumes actual joint continuity and actual pointwise derivatives. -/
lemma hasDerivAt_integral_compact {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) (∫ x, df t x ∂μ) t := by
  have htc : IsCompact (Icc (t-1) (t+1) ×ˢ (univ : Set S)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := (htc.image hd).isBounded.exists_norm_le
  have hmeas (u : ℝ) : AEStronglyMeasurable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (df t) μ :=
    (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Icc (t-1) (t+1)) (bound := fun _ ↦ C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall hmeas)
    (continuous_integrable (hf.comp (continuous_const.prodMk continuous_id))) hDmeas
    (Eventually.of_forall fun x u hu ↦ hC _ ⟨(u,x), ⟨hu, mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun x u _ ↦ hfd u x)).2

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


theorem solution : type_of% @_root_.OAI.KervaireHaarFlow.hasDerivAt_integral_compact := @_root_.OAI.KervaireHaarFlow.hasDerivAt_integral_compact
