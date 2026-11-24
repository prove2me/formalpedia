-- Prove2me | solution 1 for GlobalTheory.FrameDet.exists_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:16.069796+00:00
-- url     : https://prove2.me/submissions/28c0f9e4-a77c-45a8-b0d5-753a03f6158c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DetDvdEquivariantFramePolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPolynomial Formalism.L2.LamCM
open GlobalTheory GlobalTheory.FrameDet
open GlobalTheory.BorelAlg
namespace GlobalTheory.FrameDet
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (x y : Matrix (Fin n) (Fin n) K) (l : Fin n) (hl : ∀ i, i ≤ l)
    (hx : x.det ≠ 0) (h : ∀ i, i ≠ l → y i = x i) :
    ∃ b : Matrix (Fin n) (Fin n) K, y = b * x ∧ (∀ i j, i < j → b i j = 0) ∧ (∀ i, i ≠ l → b i i = 1) ∧
      b.det = b l l := by
  have hrow : ∀ i, i ≠ l → ∀ j, (y * x⁻¹) i j = (1 : Matrix _ _ K) i j := by
    intro i hi j
    rw [← Matrix.mul_nonsing_inv _ hx.isUnit]
    simp only [Matrix.mul_apply, h i hi]
  have hb : ∀ i j, i < j → (y * x⁻¹) i j = 0 := fun i j hij => by
    rw [hrow i (hij.trans_le (hl j)).ne, Matrix.one_apply_ne hij.ne]
  refine ⟨y * x⁻¹, ?_, hb, fun i hi => by rw [hrow i hi, Matrix.one_apply_eq], ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx.isUnit, Matrix.mul_one]
  · rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hb i j hij), Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow i hi, Matrix.one_apply_eq]
    · simp
end GlobalTheory.FrameDet
