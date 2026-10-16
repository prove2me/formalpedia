-- Prove2me | solution 1 for OAI.GAD.exists_projected_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:14:47.627996+00:00
-- url     : https://prove2.me/submissions/0c3434d4-bf1d-4c9f-a744-e21ac5b2bff4

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean:L290-L327
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_projected_factor. The node keeps its source
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
omit [Fintype ι] [Fintype κ] in
theorem frobVector_sub (A B : Matrix ι κ ℂ) : frobVector (A-B)=frobVector A-frobVector B := rfl

variable [DecidableEq ι]

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

theorem mass_sub (A B : Matrix ι κ ℂ) :
    mass (A-B)=mass A+mass B-2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_sub_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_sub,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

theorem mass_eq_zero (A : Matrix ι κ ℂ) : mass A=0 ↔ A=0 := by
  rw [← frobVector_norm,sq_eq_zero_iff,norm_eq_zero]
  constructor
  · intro h; ext i k; exact congrArg (fun v : EuclideanSpace ℂ (ι × κ) ↦ v (i,k)) h
  · intro h; subst A; rfl

theorem projection_inner {P : Matrix ι ι ℂ} (hP : IsProjection P) (X : Matrix ι κ ℂ) :
    ⟪frobVector X,frobVector (P*X)⟫_ℝ=mass (P*X) := by
  have h := projection_orthogonal hP X X
  rw [frobVector_sub,inner_sub_right,real_inner_self_eq_norm_sq,
    frobVector_norm,real_inner_comm] at h
  linarith

/-- Normalize a successful projection without losing more than twice its failure mass. -/
theorem exists_projected_factor {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (X B : Matrix ι κ ℂ) (hX : mass X=1) (hB : mass B=1) (hPB : P*B=B) :
    ∃ Y : Matrix ι κ ℂ, mass Y=1 ∧ P*Y=Y ∧ mass (X-Y) ≤ 2*(1-mass (P*X)) := by
  let p := mass (P*X)
  have hp0 : 0 ≤ p := mass_nonneg _
  have hp1 : p ≤ 1 := by simpa only [hX] using projection_mass_le hP X
  by_cases hp : p=0
  · refine ⟨B,hB,hPB,?_⟩
    have hz : P*X=0 := (mass_eq_zero _).mp hp
    have hi := projection_orthogonal hP B X
    rw [hPB,hz,sub_zero,real_inner_comm] at hi
    rw [mass_sub,hX,hB,hi]
    change 1+1-2*0 ≤ 2*(1-p)
    rw [hp]; norm_num
  · have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpp
    let a : ℝ := (Real.sqrt p)⁻¹
    refine ⟨a • (P*X), ?_, ?_, ?_⟩
    · rw [mass_real_smul]
      change (Real.sqrt p)⁻¹^2*p=1
      rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
    · rw [Matrix.mul_smul,← Matrix.mul_assoc,hP.2]
    · rw [mass_sub,mass_real_smul,hX]
      have he : a^2*mass (P*X)=1 := by
        change (Real.sqrt p)⁻¹^2*p=1
        rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
      rw [he]
      change 1+1-2*⟪frobVector X,a • frobVector (P*X)⟫_ℝ ≤ 2*(1-p)
      rw [real_inner_smul_right,projection_inner hP X]
      have hsp : p ≤ Real.sqrt p := by nlinarith [Real.sq_sqrt hp0,(Real.sqrt_nonneg p)]
      have hprod : a*p=Real.sqrt p := by
        dsimp [a]
        calc
          _ = (Real.sqrt p)⁻¹ * (Real.sqrt p*Real.sqrt p) := by congr 1; nlinarith [Real.sq_sqrt hp0]
          _ = _ := by field_simp
      change 1+1-2*(a*p) ≤ 2*(1-p)
      rw [hprod]; linarith

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.exists_projected_factor := @_root_.OAI.GAD.exists_projected_factor
