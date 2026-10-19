-- Prove2me | solution 2 for OAI.KervaireSignPairing.sign_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:35:11.928729+00:00
-- url     : https://prove2.me/submissions/3a7b54a2-d074-462e-a57b-387deff0267c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SignedIncidence.lean:L215-L227
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSignPairing.sign_count. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence

-- ---- from OAI.GroupTheory.Kervaire.SignedIncidence ----
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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireIncidenceCurrent

section
open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

end

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

end

open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
end KervaireIncidenceCurrent

namespace KervaireSignPairing

section
open Matrix
variable {I K : Type*} [Fintype I]

lemma sign_count (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (h : ∑ i, s i = 1) : Fintype.card (positive s) = Fintype.card (negative s) + 1 := by
  classical
  have hp : (∑ i : positive s, s i) = (Fintype.card (positive s) : ℤ) := by
    simp only [show (fun i : positive s ↦ s i) = fun _ ↦ (1 : ℤ) from
      funext (fun i ↦ i.property),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hn : (∑ i : negative s, s i) = -(Fintype.card (negative s) : ℤ) := by
    simp only [show (fun i : negative s ↦ s i) = fun _ ↦ (-1 : ℤ) from
      funext (fun i ↦ (hs i).resolve_left i.property),Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_neg,mul_one]
  have hc := Fintype.sum_subtype_add_sum_subtype (fun i ↦ s i = 1) s
  rw [hp,hn,h] at hc
  omega

end

open Matrix KervaireIncidenceCurrent KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K D : Type*} [Fintype I] [Fintype K] [Fintype D]
  [DecidableEq I] [DecidableEq K] [DecidableEq D]

end KervaireSignPairing

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSignPairing
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
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix


theorem solution : type_of% @_root_.OAI.KervaireSignPairing.sign_count := @_root_.OAI.KervaireSignPairing.sign_count
