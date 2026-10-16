-- Prove2me | solution 1 for OAI.GAD.projected_self_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:44:43.613422+00:00
-- url     : https://prove2.me/submissions/81c28f31-202c-467d-a3ff-adf18ee3fc3a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean:L100-L112
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.projected_self_failure. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Theorems.Thm_OAI_GAD_frobVector_inner

-- ---- from OAI.InformationTheory.AmplitudeDamping.GramMatrices ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

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

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_nonneg (A : Matrix ι κ ℂ) : 0 ≤ mass A :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose A).trace_nonneg).1

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

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
variable [DecidableEq ι]

theorem IsProjection.complement {P : Matrix ι ι ℂ} (hP : IsProjection P) : IsProjection (1-P) := by
  refine ⟨(Matrix.isHermitian_one).sub hP.1, ?_⟩
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP.2]
  simp

omit [DecidableEq ι] in
theorem projection_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P) (A B : Matrix ι κ ℂ) :
    ⟪frobVector (P*A),frobVector (B-P*B)⟫_ℝ=0 := by
  rw [frobVector_inner,Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_sub]
  have he : Aᴴ*P*(P*B)=Aᴴ*P*B := by
    rw [← Matrix.mul_assoc _ P,Matrix.mul_assoc Aᴴ P P,hP.2]
  rw [he,sub_self,Matrix.trace_zero,Complex.zero_re]

omit [DecidableEq ι] in
theorem projection_mass_decomposition {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A)+mass (A-P*A)=mass A := by
  have h := norm_add_sq_real (frobVector (P*A)) (frobVector (A-P*A))
  rw [← frobVector_add,projection_orthogonal hP A A,mul_zero,add_zero] at h
  have he : P*A+(A-P*A)=A := by abel
  rw [he,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

omit [DecidableEq ι] in
theorem projection_mass_le {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A) ≤ mass A := by
  have h := projection_mass_decomposition hP A
  linarith [mass_nonneg (A-P*A)]

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem mass_real_smul (a : ℝ) (A : Matrix ι κ ℂ) : mass (a • A)=a^2*mass A := by
  rw [← frobVector_norm,← frobVector_norm]
  have he : frobVector (a • A)=a • frobVector A := rfl
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem mass_add (A B : Matrix ι κ ℂ) :
    mass (A+B)=mass A+mass B+2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.SequentialMatrices ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mass_triangle_sq (X Y : Matrix ι κ ℂ) : mass (X+Y) ≤ 2*mass X+2*mass Y := by
  have h := norm_sub_sq_real (frobVector X) (frobVector Y)
  rw [mass_add,← frobVector_norm X,← frobVector_norm Y]
  nlinarith [sq_nonneg ‖frobVector X-frobVector Y‖]

theorem projected_self_failure {P Q : Matrix ι ι ℂ} (hQ : IsProjection Q)
    (F : Matrix ι κ ℂ) : mass (P*F-Q*(P*F)) ≤ 2*mass (F-Q*F)+2*mass (F-P*F) := by
  have he : P*F-Q*(P*F)=(F-Q*F)+(-(1-Q)*(F-P*F)) := by
    simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub]
    abel
  rw [he]
  have hb := mass_triangle_sq (F-Q*F) (-(1-Q)*(F-P*F))
  have hn : mass (-(1-Q)*(F-P*F))=mass ((1-Q)*(F-P*F)) := by
    rw [Matrix.neg_mul,← neg_one_smul ℝ ((1-Q)*(F-P*F)),mass_real_smul]
    norm_num
  rw [hn] at hb
  have hc := projection_mass_le hQ.complement (F-P*F)
  linarith

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.projected_self_failure := @_root_.OAI.GAD.projected_self_failure
