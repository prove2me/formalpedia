-- Prove2me | solution 1 for GlobalTheory.EigFlat.eig_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:51.35825+00:00
-- url     : https://prove2.me/submissions/31847817-d717-4d09-ae4a-af0172d5d8e1

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
theorem _root_.solution {g m : ℕ} (u : Fin m → Fin g → A) (M : Matrix (Fin g) (Fin g) A) (ρ : A)
    (hu : ∀ k, u k ᵥ* M = ρ • u k) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (cf ᵥ* (Matrix.of u).map (algebraMap A B)) ᵥ* M.map (algebraMap A B)
      = algebraMap A B ρ • (cf ᵥ* (Matrix.of u).map (algebraMap A B)) := by
  have h : Matrix.of u * M = ρ • Matrix.of u := by
    ext k j
    exact congrFun (hu k) j
  have h2 : (ρ • Matrix.of u).map (algebraMap A B)
      = algebraMap A B ρ • (Matrix.of u).map (algebraMap A B) := by
    ext i j; simp
  rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, h, h2, Matrix.vecMul_smul]
end GlobalTheory.EigFlat
