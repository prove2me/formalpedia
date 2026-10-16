-- Prove2me | solution 1 for OAI.GAD.entropy_le_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:31:07.458215+00:00
-- url     : https://prove2.me/submissions/70369e92-d4f8-4e76-b10f-dbaf9204de57

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean:L74-L91
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_le_diagonal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

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

/-- The square-moduli in each row of a unitary matrix sum to one. -/
theorem unitary_row_sq_sum (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The ordinary diagonal is a doubly stochastic mixing of the spectral diagonal. -/
theorem diag_eq_spectral_mix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    (A i i).re = ∑ j, Complex.normSq (hA.eigenvectorUnitary i j) * hA.eigenvalues j := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.mul_diagonal, Matrix.star_apply, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

/-- Pinching in any fixed orthonormal coordinate basis increases entropy. -/
theorem entropy_le_diagonal {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    entropy A ≤ ∑ i, Real.negMulLog (A i i).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hi (i : ι) :
      ∑ j, Complex.normSq (U i j) * Real.negMulLog (hA.isHermitian.eigenvalues j) ≤
        Real.negMulLog (A i i).re := by
    rw [diag_eq_spectral_mix hA.isHermitian]
    simpa only [U, smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
        (w := fun j ↦ Complex.normSq (U i j))
        (p := hA.isHermitian.eigenvalues) (fun j _ ↦ Complex.normSq_nonneg _)
        (by simpa using unitary_row_sq_sum U i)
        (fun j _ ↦ hA.eigenvalues_nonneg j)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  rw [Finset.sum_comm] at h
  simp only [← Finset.sum_mul, unitary_col_sq_sum, one_mul] at h
  rwa [entropy_eq_sum hA.isHermitian]

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
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_le_diagonal := @_root_.OAI.GAD.entropy_le_diagonal
