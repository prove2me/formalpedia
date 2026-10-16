-- Prove2me | solution 1 for OAI.GAD.exists_orthogonal_factors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:18:38.092991+00:00
-- url     : https://prove2.me/submissions/b6bc087c-43a5-419e-bf97-5df0c4758563

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean:L55-L71
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_orthogonal_factors. The node keeps its source
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
import Theorems.Thm_OAI_GAD_exists_projected_factor
import Theorems.Thm_OAI_GAD_spectralFactor_gram

-- ---- from OAI.InformationTheory.AmplitudeDamping.BlockFactors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

theorem blockProjection_isProjection (m : μ) : IsProjection (blockProjection (ι := ι) m) := by
  constructor
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro im; split_ifs <;> simp
  · rw [blockProjection,Matrix.diagonal_mul_diagonal]
    congr 1; funext im; split_ifs <;> simp

omit [Fintype κ] in
theorem blockProjection_mul (m : μ) (X : Matrix (ι × μ) κ ℂ) (ia : ι × μ) (j : κ) :
    (blockProjection (ι := ι) m*X) ia j=if ia.2=m then X ia j else 0 := by
  simp [blockProjection,Matrix.diagonal_mul]

omit [Fintype κ] [Fintype μ] in
theorem blockInjection_mul (m : μ) (X : Matrix ι κ ℂ) (ia : ι × μ) (j : κ) :
    (blockInjection (ι := ι) m*X) ia j=if ia.2=m then X ia.1 j else 0 := by
  simp [blockInjection,Matrix.mul_apply,ite_mul]

theorem blockInjection_isometry (m : μ) :
    (blockInjection (ι := ι) m)ᴴ*blockInjection (ι := ι) m=1 := by
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,blockInjection]
  simp [Matrix.one_apply,eq_comm]

theorem mass_isometry {ρ : Type u_6} [Fintype ρ] (W : Matrix ρ ι ℂ)
    (hW : Wᴴ*W=1) (X : Matrix ι κ ℂ) : mass (W*X)=mass X := by
  dsimp [mass,gram]
  rw [Matrix.conjTranspose_mul,Matrix.trace_mul_comm]
  have h : Xᴴ*Wᴴ*(W*X)=Xᴴ*X := by
    rw [← Matrix.mul_assoc _ W,Matrix.mul_assoc Xᴴ, hW,Matrix.mul_one]
  rw [h,Matrix.trace_mul_comm]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.Naimark ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

omit [DecidableEq μ] in
theorem naimark_isometry (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (hDs : ∑ m, D m=1) : (naimark D hD)ᴴ*naimark D hD=1 := by
  rw [← hDs]
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,naimark,star_star,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun A : Matrix ι ι ℂ ↦ A i j) (spectralFactor_gram (hD m))

theorem naimark_block (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (X : Matrix ι ι ℂ) (m : μ) :
    blockProjection (ι := ι) m*(naimark D hD*X)=
      blockInjection (ι := ι) m*((spectralFactor (hD m))ᴴ*X) := by
  ext im j
  rw [blockProjection_mul,blockInjection_mul]
  split_ifs with h
  · simp only [Matrix.mul_apply,naimark,h,Matrix.conjTranspose_apply]
  · rfl

theorem naimark_success (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (X : Matrix ι ι ℂ) (m : μ) :
    mass (blockProjection (ι := ι) m*(naimark D hD*X))=(D m*gram X).trace.re := by
  rw [naimark_block,mass_isometry _ (blockInjection_isometry m)]
  dsimp only [mass,gram]
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_cycle]
  have hF : spectralFactor (hD m)*(spectralFactor (hD m))ᴴ=D m := spectralFactor_gram (hD m)
  rw [Matrix.mul_assoc Xᴴ (spectralFactor (hD m)) _,hF,Matrix.trace_mul_cycle,Matrix.trace_mul_comm (X*Xᴴ)]

theorem blockProjection_injection (m : μ) (X : Matrix ι ι ℂ) :
    blockProjection (ι := ι) m*(blockInjection (ι := ι) m*X)=blockInjection (ι := ι) m*X := by
  ext im j
  rw [blockProjection_mul,blockInjection_mul]
  split_ifs <;> rfl

/-- Approximate orthogonalization of well decoded states in a Naimark dilation. -/
theorem exists_orthogonal_factors (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1) :
    ∃ Y : μ → Matrix (ι × μ) ι ℂ,
      (∀ m, mass (Y m)=1) ∧ (∀ m, blockProjection (ι := ι) m*Y m=Y m) ∧
      (∀ m, mass (naimark D hD*spectralFactor (hA m).1-Y m) ≤ 2*(1-(D m*A m).trace.re)) := by
  have hm (m : μ) : mass (spectralFactor (hA m).1)=1 := by
    dsimp [mass]
    rw [spectralFactor_gram,(hA m).2,Complex.one_re]
  have hy (m : μ) := exists_projected_factor (blockProjection_isProjection m)
    (naimark D hD*spectralFactor (hA m).1) (blockInjection (ι := ι) m*spectralFactor (hA m).1)
    (by rw [mass_isometry _ (naimark_isometry D hD hDs),hm])
    (by rw [mass_isometry _ (blockInjection_isometry m),hm])
    (blockProjection_injection m _)
  choose Y hY hPY hd using hy
  refine ⟨Y,hY,hPY,fun m ↦ ?_⟩
  simpa only [naimark_success,spectralFactor_gram] using hd m

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.exists_orthogonal_factors := @_root_.OAI.GAD.exists_orthogonal_factors
