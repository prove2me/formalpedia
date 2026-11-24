-- Prove2me | solution 1 for GlobalTheory.UnitaryOrbitForm.exists_unitary_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:12.048864+00:00
-- url     : https://prove2.me/submissions/3e5c9924-3601-4709-a0bc-2f1d1cecc8c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
private lemma transpose_col_mul_mul_map_conj_apply (B : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) (i j : Fin 1) :
    ((Matrix.of fun k (_ : Fin 1) => x k)ᵀ * B *
      (Matrix.of fun k (_ : Fin 1) => x k).map (starRingEnd ℂ)) i j = x ⬝ᵥ B *ᵥ star x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, dotProduct,
    mulVec, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma of_col_mulVec_eq_smul (x : Fin r → ℂ) (a : Fin 1 → ℂ) :
    (Matrix.of fun k (_ : Fin 1) => x k) *ᵥ a = a 0 • x := by
  ext i
  simp [mulVec, dotProduct, mul_comm]
private lemma mul_of_col_eq_of_mulVec (g : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) :
    g * (Matrix.of fun k (_ : Fin 1) => x k) = Matrix.of fun k (_ : Fin 1) => (g *ᵥ x) k := by
  ext i j
  simp [Matrix.mul_apply, mulVec, dotProduct]
end GlobalTheory.UnitaryOrbitForm
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
namespace GlobalTheory.UnitaryOrbitForm
theorem _root_.solution {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) {v w : Fin r → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᵀ * B * g.map (starRingEnd ℂ) = B ∧ g *ᵥ v = w := by
  have hG : ∀ a b, starRingEnd ℂ (B a b) = B b a := fun a b => by
    rw [starRingEnd_apply]
    exact hB.apply b a
  have h0 : ∀ a : Fin 1 → ℂ, (Matrix.of fun k (_ : Fin 1) => v k) *ᵥ a = 0 ↔
      (Matrix.of fun k (_ : Fin 1) => w k) *ᵥ a = 0 := by
    intro a
    rw [of_col_mulVec_eq_smul, of_col_mulVec_eq_smul, smul_eq_zero, smul_eq_zero]
    simp [hv, hw]
  have hXY : (Matrix.of fun k (_ : Fin 1) => w k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => w k).map (starRingEnd ℂ) =
      (Matrix.of fun k (_ : Fin 1) => v k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => v k).map (starRingEnd ℂ) := by
    ext i j
    rw [transpose_col_mul_mul_map_conj_apply, transpose_col_mul_mul_map_conj_apply, h]
  obtain ⟨γ, hγ, hγX⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq two_ne_zero
    (fun t => Complex.conj_conj t) hG hdet h0 hXY
  refine ⟨γ, hγ, ?_⟩
  rw [mul_of_col_eq_of_mulVec] at hγX
  funext i
  simpa using congrFun (congrFun hγX i) 0
end GlobalTheory.UnitaryOrbitForm
