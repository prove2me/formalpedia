-- Prove2me | solution 1 for OAI.GAD.entropy_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:01:29.479396+00:00
-- url     : https://prove2.me/submissions/c80a9c0b-0107-4f88-8f11-f260859ce1c4

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean:L65-L78
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_reindex. The node keeps its source
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

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

theorem entropy_reindex (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Matrix.reindex e e A) = entropy A := by
  let φ := reindexStarAlgEquiv e
  have hφA : (φ A).IsHermitian := hA.submatrix e.symm
  have hm := StarAlgHomClass.map_cfc (S := ℂ) φ Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous φ by
      change Continuous (fun A : Matrix ι ι ℂ ↦ A.submatrix e.symm e.symm)
      fun_prop) hA hφA
  unfold entropy
  change (cfc Real.negMulLog (φ A)).trace.re = _
  calc
    _ = (φ (cfc Real.negMulLog A)).trace.re := congrArg (fun B : Matrix κ κ ℂ ↦ B.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_reindex e _)

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


theorem solution : type_of% @_root_.OAI.GAD.entropy_reindex := @_root_.OAI.GAD.entropy_reindex
