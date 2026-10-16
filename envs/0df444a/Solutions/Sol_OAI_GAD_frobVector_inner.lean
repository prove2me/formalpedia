-- Prove2me | solution 1 for OAI.GAD.frobVector_inner
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:09:59.028817+00:00
-- url     : https://prove2.me/submissions/b59102d1-1892-410c-b555-2568748b0dc7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean:L31-L48
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.frobVector_inner. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity

-- ---- from OAI.InformationTheory.AmplitudeDamping.EntropyContinuity ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

theorem mass_eq_sum_normSq (A : Matrix ι κ ℂ) : mass A=∑ i, ∑ k, Complex.normSq (A i k) := by
  simp [mass,gram,Matrix.trace,Matrix.mul_apply,Complex.mul_conj]

theorem frobVector_norm (A : Matrix ι κ ℂ) : ‖frobVector A‖^2=mass A := by
  rw [EuclideanSpace.norm_sq_eq,mass_eq_sum_normSq]
  simp only [Fintype.sum_prod_type,frobVector,PiLp.toLp_apply,Complex.sq_norm]

omit [Fintype ι] [Fintype κ] in
theorem frobVector_add (A B : Matrix ι κ ℂ) : frobVector (A+B)=frobVector A+frobVector B := rfl
theorem frobVector_inner (A B : Matrix ι κ ℂ) :
    ⟪frobVector A,frobVector B⟫_ℝ=(Aᴴ*B).trace.re := by
  have hn := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at hn
  have hm : mass (A+B)=mass A+mass B+2*(Aᴴ*B).trace.re := by
    rw [mass_eq_sum_normSq,mass_eq_sum_normSq,mass_eq_sum_normSq]
    simp only [Matrix.add_apply,Complex.normSq_add,Finset.sum_add_distrib,← Finset.mul_sum]
    congr 1
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.star_def]
    ring
  linarith

variable [DecidableEq ι]

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.frobVector_inner := @_root_.OAI.GAD.frobVector_inner
