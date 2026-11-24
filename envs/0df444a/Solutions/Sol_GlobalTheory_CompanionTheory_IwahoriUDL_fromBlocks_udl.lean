-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.fromBlocks_udl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:57.440477+00:00
-- url     : https://prove2.me/submissions/0d492796-1765-4827-8716-b5ed9ebaed2c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.IwahoriUDL
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (c : Matrix (Fin n) (Fin 1) R)
    (r : Matrix (Fin 1) (Fin n) R) (a b : Matrix (Fin 1) (Fin 1) R) (hab : a * b = 1)
    (hba : b * a = 1) (u d l : Matrix (Fin n) (Fin n) R) (h : A - c * b * r = u * d * l) :
    fromBlocks A c r a =
      fromBlocks u (c * b) 0 1 * fromBlocks d 0 0 a * fromBlocks l 0 (b * r) 1 := by
  have h' : A = u * d * l + c * b * r := by rw [← h]; abel
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.mul_assoc c b a, hba, Matrix.mul_one, ← Matrix.mul_assoc a b r, hab, Matrix.one_mul]
  rw [h', Matrix.mul_assoc c b r]
end GlobalTheory.CompanionTheory.IwahoriUDL
