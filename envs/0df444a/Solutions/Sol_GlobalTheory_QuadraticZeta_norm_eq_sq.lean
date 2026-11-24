-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.norm_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:16.110534+00:00
-- url     : https://prove2.me/submissions/67a68787-3306-426b-9d2f-dbb62ff47a28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis_embedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_det_mul_im
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (x : K) : (Algebra.norm ℚ x : ℝ) = ‖σ x‖ ^ 2 := by
  obtain ⟨b, t, h0, -, hi⟩ := exists_basis_embedding h2 hD σ
  have hd := discr_pos h2 hD
  have hi0 : (σ (b 1)).im ≠ 0 := fun h => by rw [h] at hi; linarith
  let b' : Basis (Fin 2) ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  have e0 : b' 0 = 1 := by simp [b', h0]
  have e1 : b' 1 = b 1 := by simp [b']
  have := det_mul_im σ b' e0 (x * b' 0) (x * b' 1)
  rw [show b'.det ![x * b' 0, x * b' 1] = Algebra.norm ℚ x by
    rw [Algebra.norm_eq_matrix_det b', Basis.det_apply]
    congr 1
    ext i j
    fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, Basis.toMatrix_apply], e0, e1] at this
  refine mul_right_cancel₀ hi0 (this.trans ?_)
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring
end GlobalTheory.QuadraticZeta
