-- Prove2me | solution 1 for OAI.KervaireCentralizer.exists_phaseOperator_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:05:53.821627+00:00
-- url     : https://prove2.me/submissions/c6c3d9c1-b141-40bf-aa3b-c151b4faa4a4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean:L160-L184
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireCentralizer.exists_phaseOperator_mem. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_exists_phaseOperator

-- ---- from OAI.GroupTheory.Kervaire.PhaseSubadditivity ----
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

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] OAI.KervaireCentralizer.instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint
end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The bounded phase logarithm stays in every operator centralizer. -/
theorem exists_phaseOperator_mem (S : Set (Operator (H := H))) (U : algebra S)
    (hU : U ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    ∃ B : algebra S, 0 ≤ B ∧ NormedSpace.exp (phaseVelocity B) = U ∧
      ∀ ξ : H, (vectorCLM ξ (B : Operator (H := H))).re = vectorPhase (U : Operator (H := H)) ξ := by
  have hU' := (unitary_iff S U).mp hU
  obtain ⟨B, hB, _, _, hexp, hvec, hcomm⟩ := exists_phaseOperator (U : Operator (H := H)) hU'
  have hBm : B ∈ algebra S := by
    rw [algebra, StarSubalgebra.mem_centralizer_iff]
    intro R hR
    have hu := (StarSubalgebra.mem_centralizer_iff ℂ).mp U.property R hR
    have hv := (StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem U.property) R hR
    exact ⟨(hcomm R hu.1.symm hv.1.symm).eq.symm,
      (hcomm (star R) hu.2.symm hv.2.symm).eq.symm⟩
  let Bs : algebra S := ⟨B, hBm⟩
  refine ⟨Bs, hB, ?_, hvec⟩
  apply Subtype.ext
  let : NormedAlgebra ℚ (Operator (H := H)) := NormedAlgebra.restrictScalars ℚ ℂ (Operator (H := H))
  let : NormedAlgebra ℚ (algebra S) := NormedAlgebra.restrictScalars ℚ ℂ (algebra S)
  rw [show ((NormedSpace.exp (phaseVelocity Bs) : algebra S) : Operator (H := H)) =
      NormedSpace.exp (phaseVelocity (Bs : Operator (H := H))) by
    exact NormedSpace.map_exp (algebra S).subtype continuous_subtype_val (phaseVelocity Bs)]
  convert hexp using 1
  simp [phaseVelocity, Bs]

end KervaireCentralizer

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireCentralizer
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireCentralizer.exists_phaseOperator_mem := @_root_.OAI.KervaireCentralizer.exists_phaseOperator_mem
