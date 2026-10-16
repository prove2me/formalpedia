-- Prove2me | solution 1 for OAI.GAD.tensorMatrix_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:35:25.976966+00:00
-- url     : https://prove2.me/submissions/89ffdb6f-9ebe-4cae-8b5d-a52b5c499125

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseProducts.lean:L51-L64
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.tensorMatrix_entropy. The node keeps its source
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
import Theorems.Thm_OAI_GAD_entropy_diagonal
import Theorems.Thm_OAI_GAD_entropy_reindex
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

end GAD
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem entropy_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    entropy (A ⊗ₖ B) = B.trace.re * entropy A + A.trace.re * entropy B := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let W := tensorUnitary U V
  let p := hA.eigenvalues
  let q := hB.eigenvalues
  have he : A ⊗ₖ B = Unitary.conjStarAlgAut ℂ _ W
      (Matrix.diagonal (fun ij : ι × κ ↦ ((p ij.1*q ij.2 : ℝ):ℂ))) := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    change _ = ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)) * _ *
      (((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)).conjTranspose)
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal]
    congr 2
    simp [p,q]
  have hd : (Matrix.diagonal (fun ij : ι × κ ↦ ((p ij.1*q ij.2 : ℝ):ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr (fun _ ↦ by simp [IsSelfAdjoint])
  rw [he, entropy_unitary_conj W hd, entropy_diagonal, Fintype.sum_prod_type]
  simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have htrA : A.trace.re = ∑ i, p i := by simpa [p] using congrArg Complex.re hA.trace_eq_sum_eigenvalues
  have htrB : B.trace.re = ∑ j, q j := by simpa [q] using congrArg Complex.re hB.trace_eq_sum_eigenvalues
  rw [htrA,htrB,entropy_eq_sum hA,entropy_eq_sum hB]
  simp [p, q, ← Finset.mul_sum]

theorem entropy_kronecker_state {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : IsState A) (hB : IsState B) : entropy (A ⊗ₖ B) = entropy A + entropy B := by
  rw [entropy_kronecker hA.1.isHermitian hB.1.isHermitian, hA.2, hB.2]
  simp

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PhaseProducts ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD

theorem tensorMatrix_entropy (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, IsState (A k)) : entropy (tensorMatrix n A) = ∑ k, entropy (A k) := by
  induction n with
  | zero =>
      rw [tensorMatrix_zero]
      have hdiag : (1 : QMatrix 0) = Matrix.diagonal (fun _ : Basis 0 ↦ (1:ℂ)) := by simp
      rw [hdiag]
      change entropy (Matrix.diagonal (fun _ : Basis 0 ↦ ((1:ℝ):ℂ))) = _
      rw [entropy_diagonal]
      simp
  | succ n ih =>
      rw [← entropy_reindex (tensorSplit n) (tensorMatrix_state (n+1) A hA).1.isHermitian,
        tensorMatrix_split,entropy_kronecker_state (hA 0)
          (tensorMatrix_state n _ (fun k ↦ hA k.succ)),ih _ (fun k ↦ hA k.succ),Fin.sum_univ_succ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.tensorMatrix_entropy := @_root_.OAI.GAD.tensorMatrix_entropy
