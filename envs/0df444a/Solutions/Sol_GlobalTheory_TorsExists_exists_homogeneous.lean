-- Prove2me | solution 1 for GlobalTheory.TorsExists.exists_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:57.367804+00:00
-- url     : https://prove2.me/submissions/c54cb52a-65ac-40e5-a0f5-77fb26f4c789

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {R : Type} [CommRing R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (hh : D * h + h * D = 1) :
    ∃ h' : Matrix Ix Ix R, (∀ p q, deg p ≠ deg q + 1 → h' p q = 0) ∧ D * h' + h' * D = 1 := by
  refine ⟨Matrix.of fun p q => if deg p = deg q + 1 then h p q else 0, fun p q hpq => by simp [hpq], ?_⟩
  ext a b
  by_cases hab : deg a = deg b
  · rw [← hh]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_
    · split_ifs with hp
      · rfl
      · rw [hD a p (by omega)]; simp
    · split_ifs with hp
      · rfl
      · rw [hD p b (by omega)]; simp
  · rw [Matrix.one_apply_ne (fun e => hab (by rw [e]))]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro p _
      split_ifs with hp
      · rw [hD p b (by omega)]; simp
      · simp
    · intro p _
      split_ifs with hp
      · rw [hD a p (by omega)]; simp
      · simp
end GlobalTheory.TorsExists
