-- Prove2me | solution 1 for OAI.GAD.det_linearDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:11:44.224855+00:00
-- url     : https://prove2.me/submissions/4ddd049b-f87a-4f9a-98a7-1f6bd936e5a1

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L22-L36
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.det_linearDeriv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Jacobi's differential, without an invertibility assumption. -/
theorem det_linearDeriv (A H : Matrix ι ι ℂ) :
    detMultilinear.linearDeriv A H = Matrix.trace (H * A.adjugate) := by
  change (detMultilinear.linearDeriv (fun i j ↦ A i j)) (fun i j ↦ H i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (A.updateRow i (H i)).det = _
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.det_linearDeriv := @_root_.OAI.GAD.det_linearDeriv
