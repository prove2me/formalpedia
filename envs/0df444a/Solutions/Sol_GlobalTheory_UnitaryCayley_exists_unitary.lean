-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.exists_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:39.594426+00:00
-- url     : https://prove2.me/submissions/8f6e8395-c3a5-4803-897a-fd255bfc434d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff
import Theorems.Thm_GlobalTheory_UnitaryCayley_trace_Jm
import Theorems.Thm_GlobalTheory_UnitaryCayley_exists_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (h2 : A * A = 1)
    (ε : Fin n → Bool) (ht : (Jm ε).trace = A.trace) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) ℂ, Pᴴ * Jm ε * P = A := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUu : U ∈ Matrix.unitaryGroup (Fin n) ℂ := hA.eigenvectorUnitary.2
  have hl : star U * U = 1 := Unitary.star_mul_self_of_mem hUu
  have hr : U * star U = 1 := Unitary.mul_star_self_of_mem hUu
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ)) with hD
  have hs : A = U * D * star U := by
    have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have hD' : D = star U * A * U := by
    rw [hs]
    calc D = (star U * U) * D * (star U * U) := by rw [hl]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hDD : D * D = 1 := by
    rw [hD']
    calc star U * A * U * (star U * A * U) = star U * (A * (U * star U) * A) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hr, Matrix.mul_one, h2, Matrix.mul_one, hl]
  have hev : ∀ i, (hA.eigenvalues i : ℂ) = 1 ∨ (hA.eigenvalues i : ℂ) = -1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    rw [hD, diagonal_mul_diagonal] at this
    simp only [diagonal_apply_eq, one_apply_eq] at this
    exact mul_self_eq_one_iff.mp this
  classical
  let δ : Fin n → Bool := fun i => decide ((hA.eigenvalues i : ℂ) = 1)
  have hJ : Jm δ = D := by
    unfold Jm
    rw [hD]; congr 1; funext i
    by_cases h : (hA.eigenvalues i : ℂ) = 1
    · simp only [δ, h]; simp
    · simp only [δ, h]; simp [(hev i).resolve_left h]
  have htr : (Jm ε).trace = (Jm δ).trace := by
    rw [ht, hJ, hD', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hr, Matrix.one_mul]
  rw [trace_Jm, trace_Jm] at htr
  have hc : (univ.filter fun i => ε i = true).card = (univ.filter fun i => δ i = true).card := by
    have : ((univ.filter fun i => ε i = true).card : ℂ) = (univ.filter fun i => δ i = true).card := by
      linear_combination htr / 2
    exact_mod_cast this
  obtain ⟨e, he⟩ := exists_perm ε δ hc
  have hJe : Jm ε = (Jm δ).submatrix e e := by
    unfold Jm
    rw [Matrix.submatrix_diagonal_equiv]; congr 1; funext a; simp [he]
  refine ⟨(star U).submatrix e id, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, star_star, hr]
    simp
  · rw [hJe, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, star_star, hJ, ← hs]
    simp
end GlobalTheory.UnitaryCayley
