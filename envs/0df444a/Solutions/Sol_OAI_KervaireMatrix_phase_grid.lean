-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:22:37.426344+00:00
-- url     : https://prove2.me/submissions/01a423c7-f706-488b-90c5-418f274d822a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean:L342-L363
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_grid. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_sum_vectorPhase_grid

-- ---- from OAI.GroupTheory.Kervaire.MatrixTrace ----
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

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
variable [Fintype D]

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

variable [Fintype D]

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

/-- Matrix trace of the root-grid phase identity, retaining the unnormalized dimension. -/
theorem phase_grid (U : Operator D A) (hU : U ∈ unitary (Operator D A))
    (d : ℕ) (hd : 0 < d) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, KervaireMatrix.phase (scalarRotation ((j.val : ℝ)/d) • U)) =
      (Fintype.card D : ℝ) * ((d : ℝ)-1)/2 + KervaireMatrix.phase (U^d) := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
  change (∑ j : Fin d, ∑ i : D,
    vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) (delta (i,(1 : A)))) = _
  rw [Finset.sum_comm]
  simp_rw [sum_vectorPhase_grid U hU d hd]
  rw [Finset.sum_add_distrib]
  congr 1
  have hn (i : D) : ‖delta (i,(1 : A))‖ = 1 := by
    simp [delta, lp.norm_single]
  simp_rw [hn]
  simp
  ring

end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular KervaireSpectral


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_grid := @_root_.OAI.KervaireMatrix.phase_grid
