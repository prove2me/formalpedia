-- Prove2me | solution 1 for OAI.GAD.entropy_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:58:08.641177+00:00
-- url     : https://prove2.me/submissions/d9c57a1d-0170-4fa3-bb1a-49235b0d42e0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean:L31-L53
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_diagonal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy

-- ---- from OAI.InformationTheory.AmplitudeDamping.TensorEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology

open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem entropy_diagonal (p : ι → ℝ) :
    entropy (Matrix.diagonal (fun i ↦ (p i : ℂ))) = ∑ i, Real.negMulLog (p i) := by
  classical
  cases isEmpty_or_nonempty ι
  · simp [entropy, Matrix.trace]
  let : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus
  let φ := diagonalStarAlgHom (ι := ι)
  have hp : IsSelfAdjoint (fun i ↦ (p i : ℂ)) := by ext i; simp
  have hd : (Matrix.diagonal (fun i ↦ (p i : ℂ))).IsHermitian := by
    exact Matrix.isHermitian_diagonal_iff.mpr (fun i ↦ by simp [IsSelfAdjoint])
  have hm := StarAlgHomClass.map_cfc (S := ℂ) φ Real.negMulLog (fun i ↦ (p i : ℂ))
    Real.continuous_negMulLog.continuousOn
    (show Continuous φ by change Continuous (Matrix.diagonal : (ι → ℂ) → Matrix ι ι ℂ); fun_prop) hp hd
  have he : cfc Real.negMulLog (fun i ↦ (p i : ℂ)) = fun i ↦ (Real.negMulLog (p i) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) Real.negMulLog _ Real.continuous_negMulLog.continuousOn hp (fun i ↦ by simp [IsSelfAdjoint])]
    ext i
    exact cfc_algebraMap (A := ℂ) (p i) Real.negMulLog
  unfold entropy
  change (cfc Real.negMulLog (φ (fun i ↦ (p i : ℂ)))).trace.re = _
  calc
    _ = (φ (cfc Real.negMulLog (fun i ↦ (p i : ℂ)))).trace.re := congrArg (fun A : Matrix ι ι ℂ ↦ A.trace.re) hm.symm
    _ = _ := by rw [he]; simp [φ, diagonalStarAlgHom, Matrix.trace_diagonal]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_diagonal := @_root_.OAI.GAD.entropy_diagonal
