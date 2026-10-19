-- Prove2me | solution 2 for OAI.KervaireMatrix.trace_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:20:48.153892+00:00
-- url     : https://prove2.me/submissions/f1d99f70-0300-4388-920d-39a3fe07ab6c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean:L111-L124
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.trace_mul_comm. The node keeps its source
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
import Theorems.Thm_OAI_KervaireMatrix_trace_mul_eq_sum_tsum

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

/-- Full cyclicity of the finite matrix regular trace. -/
theorem trace_mul_comm {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    trace (S*T) = trace (T*S) := by
  rw [trace_mul_eq_sum_tsum hS, trace_mul_eq_sum_tsum hT, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑' x : A, S (delta (i,1)) (j,x⁻¹) * T (delta (j,1)) (i,x)) =
        ∑' x : A, S (delta (i,1)) (j,x) * T (delta (j,1)) (i,x⁻¹) := by
      simpa using (Equiv.inv A).tsum_eq
        (fun x : A => S (delta (i,1)) (j,x) * T (delta (j,1)) (i,x⁻¹))
    _ = _ := tsum_congr fun _ => mul_comm _ _

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
open KervaireRegular


theorem solution : type_of% @_root_.OAI.KervaireMatrix.trace_mul_comm := @_root_.OAI.KervaireMatrix.trace_mul_comm
