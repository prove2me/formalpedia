-- Prove2me | solution 1 for OAI.GAD.spectral_pure_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:06:49.253978+00:00
-- url     : https://prove2.me/submissions/2bba078c-54e6-41e7-90f4-014dc14f8131

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean:L24-L36
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.spectral_pure_decomposition. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy

-- ---- from OAI.InformationTheory.AmplitudeDamping.StateEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem spectral_pure_decomposition {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    P = ∑ a, hP.eigenvalues a • pure (fun i ↦ hP.eigenvectorUnitary i a) := by
  conv_lhs => rw [hP.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  ext i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.sum_apply,
    Matrix.smul_apply,pure,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [diagonal_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change hP.eigenvectorUnitary i a * (hP.eigenvalues a : ℂ) * star (hP.eigenvectorUnitary j a) =
    (hP.eigenvalues a : ℂ) * (hP.eigenvectorUnitary i a * star (hP.eigenvectorUnitary j a))
  ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.spectral_pure_decomposition := @_root_.OAI.GAD.spectral_pure_decomposition
