-- Prove2me | solution 1 for OAI.KervaireSpectral.vectorPhase_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:10:52.833929+00:00
-- url     : https://prove2.me/submissions/1127e3af-c4ae-4341-90c1-37af783b3cc8

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean:L143-L161
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.vectorPhase_rotation. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_vectorPhase_cfcHom

-- ---- from OAI.GroupTheory.Kervaire.PhaseNaturality ----
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

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar-rotation formula for the exact spectral measure. -/
theorem vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (x : ℝ) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨scalarRotation x,
      scalarRotation_unitary x⟩ hU)
    vectorPhase (scalarRotation x • U) ξ =
      ∫ z, phase (scalarRotation x * (z : ℂ)) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := scalarRotation x •
    (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hf : cfcHom hN f = scalarRotation x • U := by
    dsimp [f]
    rw [map_smul, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := by
    rw [hf]
    exact Unitary.smul_mem ⟨scalarRotation x, scalarRotation_unitary x⟩ hU
  simpa only [hf, f, ContinuousMap.smul_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply, smul_eq_mul] using vectorPhase_cfcHom U f hu ξ

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder


theorem solution : type_of% @_root_.OAI.KervaireSpectral.vectorPhase_rotation := @_root_.OAI.KervaireSpectral.vectorPhase_rotation
