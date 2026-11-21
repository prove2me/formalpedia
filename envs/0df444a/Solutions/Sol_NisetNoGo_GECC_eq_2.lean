-- Prove2me | solution 1 for NisetNoGo.GECC.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-20T22:39:42.528575+00:00
-- url     : https://prove2.me/submissions/e707191a-c25b-4517-ae8a-5775db346b3c

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

set_option autoImplicit false

open QAlgorithms.Papers.Independent.Frontier30.P13
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open scoped ComplexOrder

namespace NisetNoGo.GECC.Eq2

/-- The position coordinate of the single mode. -/
abbrev X : ModeQuadrature (Fin 1) := (0, false)

/-- The momentum coordinate of the single mode. -/
abbrev P : ModeQuadrature (Fin 1) := (0, true)

theorem sum_mq {β : Type*} [AddCommMonoid β] (f : ModeQuadrature (Fin 1) → β) :
    ∑ i, f i = f X + f P := by
  rw [Fintype.sum_prod_type]
  simp [add_comm]

/-- The determinant of a matrix on the two coordinates of one mode. -/
theorem det_mq {R : Type*} [CommRing R]
    (A : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) R) :
    A.det = A X X * A P P - A X P * A P X := by
  let e : Fin 2 ≃ ModeQuadrature (Fin 1) :=
    finTwoEquiv.trans (Equiv.uniqueProd Bool (Fin 1)).symm
  rw [← Matrix.det_submatrix_equiv_self e A, Matrix.det_fin_two]
  rfl

end NisetNoGo.GECC.Eq2

open NisetNoGo.GECC NisetNoGo.GECC.Eq2 Matrix in
theorem solution
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N) :
    N.PosSemidef ∧ (M.det - 1) ^ 2 ≤ N.det := by
  obtain ⟨hsym, hpsd⟩ := hT
  have hb : N P X = N X P := by
    have := congrFun (congrFun hsym X) P
    simpa [Matrix.transpose_apply] using this
  have hMdet : M.det = M X X * M P P - M X P * M P X := det_mq M
  -- the entries of the Hermitian matrix `N - i (J - M J Mᵀ)`
  have hXX : (complexify N - Complex.I • complexify
      (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)) X X = (N X X : ℂ) := by
    simp [complexify, phaseJ, Matrix.mul_apply, sum_mq]
    ring
  have hPP : (complexify N - Complex.I • complexify
      (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)) P P = (N P P : ℂ) := by
    simp [complexify, phaseJ, Matrix.mul_apply, sum_mq]
    ring
  have hXP : (complexify N - Complex.I • complexify
      (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)) X P =
      (N X P : ℂ) + Complex.I * ((1 - M.det : ℝ) : ℂ) := by
    rw [hMdet]
    simp [complexify, phaseJ, Matrix.mul_apply, sum_mq]
    ring
  have hPX : (complexify N - Complex.I • complexify
      (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)) P X =
      (N X P : ℂ) - Complex.I * ((1 - M.det : ℝ) : ℂ) := by
    rw [hMdet]
    simp [complexify, phaseJ, Matrix.mul_apply, sum_mq, hb]
    ring
  -- the determinant of a positive semidefinite matrix is nonnegative
  have hdet := hpsd.det_nonneg
  rw [det_mq, hXX, hPP, hXP, hPX] at hdet
  have e : (N X X : ℂ) * (N P P : ℂ) -
      ((N X P : ℂ) + Complex.I * ((1 - M.det : ℝ) : ℂ)) *
        ((N X P : ℂ) - Complex.I * ((1 - M.det : ℝ) : ℂ)) =
      ((N X X * N P P - N X P ^ 2 - (1 - M.det) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [e] at hdet
  have hre : 0 ≤ N X X * N P P - N X P ^ 2 - (1 - M.det) ^ 2 := by exact_mod_cast hdet
  refine ⟨?_, ?_⟩
  · -- `N` is positive semidefinite: evaluate the Hermitian form on real vectors
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hsym
    · intro x
      have h := hpsd.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
      have e2 : star (fun i => (x i : ℂ)) ⬝ᵥ
          ((complexify N - Complex.I • complexify
            (phaseJ (Fin 1) - M * phaseJ (Fin 1) * M.transpose)) *ᵥ fun i => (x i : ℂ)) =
          ((star x ⬝ᵥ (N *ᵥ x) : ℝ) : ℂ) := by
        simp only [dotProduct, Matrix.mulVec, sum_mq, hXX, hPP, hXP, hPX, hb, Pi.star_apply]
        simp
        ring
      rw [e2] at h
      exact_mod_cast h
  · rw [det_mq N, hb]
    nlinarith [hre]
