-- Prove2me | solution 1 for GlobalTheory.KeyKa.graded_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:08.460963+00:00
-- url     : https://prove2.me/submissions/3da9adb1-0735-4c01-99ea-2701a2356ced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ)
    (G G' : Matrix Ix Ix R) (hG : ∀ p q, deg p ≠ deg q → G p q = 0) (hGG : G * G' = 1) :
    ∀ p q, deg p ≠ deg q → G' p q = 0 := by
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  let G'' : Matrix Ix Ix R := Matrix.of fun p q => if deg p = deg q then G' p q else 0
  have h1 : G * G'' = 1 := by
    ext p q
    by_cases hpq : deg p = deg q
    · rw [← hGG, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : deg r = deg q
      · simp [G'', hr]
      · rw [hG p r (by omega)]; simp
    · rw [Matrix.mul_apply, Matrix.one_apply_ne (by rintro rfl; exact hpq rfl)]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : deg r = deg q
      · rw [hG p r (by omega)]; simp
      · simp [G'', hr]
  have h2 : G' = G'' := by
    calc G' = G' * (G * G'') := by rw [h1, Matrix.mul_one]
      _ = G'' := by rw [← Matrix.mul_assoc, hGG', Matrix.one_mul]
  intro p q hpq
  rw [h2]; simp [G'', hpq]
end GlobalTheory.KeyKa
