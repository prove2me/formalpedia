-- Prove2me | solution 2 for OAI.KervaireIncidenceCurrent.model_fiber_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:26:01.538431+00:00
-- url     : https://prove2.me/submissions/2b32873f-8c39-431e-88c2-1b924741a236

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean:L94-L124
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.model_fiber_blocks. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.IncidenceDegree ----
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

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The only incidence fiber over the identity is the connected gauge orbit. -/
lemma model_fiber_blocks (X A : Mat K) (B : Matrix K R ℂ) (C : Matrix R K ℂ)
    (D T : Mat R) (hQ : fromBlocks A B C D ∈ unitary (Mat (K ⊕ R)))
    (heq : diag X (-1) * fromBlocks A B C D = fromBlocks A B C D * diag 1 T) :
    X = 1 ∧ B = 0 ∧ C = 0 ∧ T = -1 ∧ A ∈ unitary (Mat K) ∧ D ∈ unitary (Mat R) := by
  have hh : X*A = A ∧ X*B = B*T ∧ -C = C ∧ -D = D*T := by
    simpa [diag, fromBlocks_multiply] using heq
  have hC : C = 0 := by
    ext i j
    have hc := congrFun (congrFun hh.2.2.1 i) j
    change -C i j = C i j at hc
    change C i j = 0
    linear_combination -(1/2 : ℂ) * hc
  subst C
  have hu := Unitary.mem_iff.mp hQ
  have hu₁ : star A*A = 1 ∧ star A*B = 0 ∧ Bᴴ*A = 0 ∧ Bᴴ*B+star D*D = 1 := by
    simpa only [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← fromBlocks_one, fromBlocks_inj] using hu.1
  have hA' : A*star A = 1 := mul_eq_one_comm.mp hu₁.1
  have hB : B = 0 := by
    have h := congrArg (fun B : Matrix K R ℂ ↦ A * B) hu₁.2.1
    simpa only [← Matrix.mul_assoc, hA', Matrix.one_mul, Matrix.mul_zero] using h
  subst B
  have hD : star D*D = 1 := by simpa using hu₁.2.2.2
  have hT : T = -1 := by
    have h := congrArg (star D * ·) hh.2.2.2
    simpa only [mul_neg, ← Matrix.mul_assoc, hD, one_mul] using h.symm
  have hX : X = 1 := by
    have h := congrArg (· * star A) hh.1
    simpa only [Matrix.mul_assoc, hA', mul_one] using h
  exact ⟨hX,rfl,rfl,hT,⟨hu₁.1,hA'⟩,⟨hD,mul_eq_one_comm.mp hD⟩⟩

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.KervaireUnitaryExponential.instNormedAlgebraRat_oAI
end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

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
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.model_fiber_blocks := @_root_.OAI.KervaireIncidenceCurrent.model_fiber_blocks
