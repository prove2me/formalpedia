-- Prove2me | solution 1 for GlobalTheory.EigFlat.eig_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:23.146862+00:00
-- url     : https://prove2.me/submissions/edc1cfac-69fe-4950-a909-15fa29acfc15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]
namespace GlobalTheory.EigFlat
theorem _root_.solution {g : ℕ} (M : Matrix (Fin g) (Fin g) A) (ρ : A) (B : Type) [CommRing B]
    [Algebra A B] (w : Fin g → B) :
    w ᵥ* (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B) = 0 ↔
      w ᵥ* M.map (algebraMap A B) = algebraMap A B ρ • w := by
  have : (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B)
      = M.map (algebraMap A B) - algebraMap A B ρ • (1 : Matrix (Fin g) (Fin g) B) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Algebra.algebraMap_eq_smul_one, sub_smul]
  rw [this, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero]
end GlobalTheory.EigFlat
