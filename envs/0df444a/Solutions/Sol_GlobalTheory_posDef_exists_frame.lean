-- Prove2me | solution 1 for GlobalTheory.posDef_exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:09.250993+00:00
-- url     : https://prove2.me/submissions/f6a08647-9edf-49be-b78d-0d2001c82dc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PosDefExistsFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ), G.PosDef →
      ∃ X : Matrix (Fin d) (Fin d) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = G := by
  intro d G hG
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]
end GlobalTheory
