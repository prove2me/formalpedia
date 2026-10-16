-- Prove2me | solution 1 for OAI.GAD.concaveOn_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:34:27.495409+00:00
-- url     : https://prove2.me/submissions/00c31daa-3089-4015-8e07-fb75dd41f966

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean:L112-L150
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.concaveOn_entropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Theorems.Thm_OAI_GAD_entropy_le_diagonal
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

/-- The full matrix entropy, not just normalized-state entropy, is concave on
positive semidefinite matrices. -/
theorem concaveOn_entropy :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} entropy := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb _
    exact (hA.smul ha).add (hB.smul hb)
  intro A hA B hB a b ha hb hab
  let C := a • A + b • B
  have hC : C.PosSemidef := (hA.smul ha).add (hB.smul hb)
  let U := hC.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hp (P : Matrix ι ι ℂ) (hP : P.PosSemidef) : (φ P).PosSemidef := by
    exact hP.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have hdiag : φ C = Matrix.diagonal (fun i ↦ (hC.isHermitian.eigenvalues i : ℂ)) := by
    exact hC.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hlin : φ C = a • φ A + b • φ B := by
    dsimp only [C]
    rw [map_add]
    congr 1 <;> exact (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
  have hs (i : ι) :
      a * Real.negMulLog ((φ A) i i).re + b * Real.negMulLog ((φ B) i i).re ≤
        Real.negMulLog (hC.isHermitian.eigenvalues i) := by
    have he : hC.isHermitian.eigenvalues i = a * ((φ A) i i).re + b * ((φ B) i i).re := by
      have ht := congrArg (fun P : Matrix ι ι ℂ ↦ (P i i).re) (hdiag.symm.trans hlin)
      simpa using ht
    rw [he]
    exact Real.concaveOn_negMulLog.2
      ((Complex.nonneg_iff.mp (hp A hA).diag_nonneg).1)
      ((Complex.nonneg_iff.mp (hp B hB).diag_nonneg).1) ha hb hab
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hs i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hEA := entropy_le_diagonal (hp A hA)
  have hEB := entropy_le_diagonal (hp B hB)
  rw [entropy_unitary_conj (star U) hA.isHermitian] at hEA
  rw [entropy_unitary_conj (star U) hB.isHermitian] at hEB
  rw [entropy_eq_sum hC.isHermitian]
  exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hEA ha)
    (mul_le_mul_of_nonneg_left hEB hb)) hsum

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


theorem solution : type_of% @_root_.OAI.GAD.concaveOn_entropy := @_root_.OAI.GAD.concaveOn_entropy
