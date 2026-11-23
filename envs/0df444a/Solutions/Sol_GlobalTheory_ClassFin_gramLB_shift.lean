-- Prove2me | solution 1 for GlobalTheory.ClassFin.gramLB_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:17.817445+00:00
-- url     : https://prove2.me/submissions/bfabefa2-3cb7-4cc7-b037-0837cde7a6b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]
end GlobalTheory.ClassFin
