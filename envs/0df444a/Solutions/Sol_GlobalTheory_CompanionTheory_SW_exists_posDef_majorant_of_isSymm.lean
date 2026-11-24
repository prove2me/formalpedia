-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:09.987795+00:00
-- url     : https://prove2.me/submissions/f69abb7d-8c28-4d0f-aa26-0d1d90c45d24

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SymmetricInvertibleExistsPosdefCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 →
      ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  intro ι _ _ B hsym hdet
  have hH : B.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℝ, U = (hH.eigenvectorUnitary : Matrix ι ι ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ι → ℝ, d = hH.eigenvalues := ⟨_, rfl⟩
  have hUs : star U * U = 1 := by subst hU; simp
  have hsU : U * star U = 1 := by subst hU; simp
  have hspec : B = U * Matrix.diagonal d * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    subst hU hdd
    simp [Unitary.conjStarAlgAut_apply]
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    rw [hdd] at hi
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have conj : ∀ a b : ι → ℝ, (U * Matrix.diagonal a * star U) * (U * Matrix.diagonal b * star U) =
      U * Matrix.diagonal (fun i => a i * b i) * star U := by
    intro a b
    calc U * Matrix.diagonal a * star U * (U * Matrix.diagonal b * star U)
        = U * Matrix.diagonal a * (star U * U) * Matrix.diagonal b * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal a * Matrix.diagonal b) * star U := by
          rw [hUs, Matrix.mul_one, Matrix.mul_assoc U]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]
  have hinv : B⁻¹ = U * Matrix.diagonal (fun i => (d i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hspec, conj]
    rw [show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) from funext fun i => mul_inv_cancel₀ (hd i),
      Matrix.diagonal_one, Matrix.mul_one, hsU]
  refine ⟨U * Matrix.diagonal (fun i => |d i|) * star U, ?_, ?_⟩
  · rw [Matrix.IsUnit.posDef_star_right_conjugate_iff ⟨⟨U, star U, hsU, hUs⟩, rfl⟩,
      Matrix.posDef_diagonal_iff]
    exact fun i => abs_pos.mpr (hd i)
  · rw [hinv, conj, conj]
    conv_rhs => rw [hspec]
    congr 3
    funext i
    show |d i| * (d i)⁻¹ * |d i| = d i
    rw [mul_right_comm, abs_mul_abs_self, mul_inv_cancel_right₀ (hd i)]
end GlobalTheory.CompanionTheory.SW
