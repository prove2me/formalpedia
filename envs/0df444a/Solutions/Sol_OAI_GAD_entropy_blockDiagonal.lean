-- Prove2me | solution 1 for OAI.GAD.entropy_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:17:03.511713+00:00
-- url     : https://prove2.me/submissions/1195aac0-be5f-4dc5-b9fe-1cc3fb32a1c6

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/BlockFactors.lean:L32-L50
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_blockDiagonal. The node keeps its source
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
import Theorems.Thm_OAI_GAD_entropy_diagonal
import Theorems.Thm_OAI_GAD_entropy_unitary_conj

-- ---- from OAI.InformationTheory.AmplitudeDamping.SpectralEntropy ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

end GAD

end

end OAI

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

theorem entropy_blockDiagonal (A : μ → Matrix ι ι ℂ) (hA : ∀ m, (A m).IsHermitian) :
    entropy (Matrix.blockDiagonal A)=∑ m, entropy (A m) := by
  let U := blockUnitary (fun m ↦ (hA m).eigenvectorUnitary)
  let d : ι × μ → ℝ := fun im ↦ (hA im.2).eigenvalues im.1
  have he : Matrix.blockDiagonal A=Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun im ↦ (d im:ℂ))) := by
    rw [Unitary.conjStarAlgAut_apply]
    change Matrix.blockDiagonal A=Matrix.blockDiagonal _*Matrix.diagonal _*(Matrix.blockDiagonal _)ᴴ
    dsimp only [d]
    rw [← Matrix.blockDiagonal_diagonal (fun m i ↦ ((hA m).eigenvalues i:ℂ)),Matrix.blockDiagonal_conjTranspose,
      ← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]
    congr 1; funext m
    exact (hA m).spectral_theorem
  have hh : (Matrix.diagonal (fun im ↦ (d im:ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro im; exact Complex.conj_ofReal _
  rw [he,entropy_unitary_conj U hh,entropy_diagonal,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact (entropy_eq_sum (hA m)).symm

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_blockDiagonal := @_root_.OAI.GAD.entropy_blockDiagonal
