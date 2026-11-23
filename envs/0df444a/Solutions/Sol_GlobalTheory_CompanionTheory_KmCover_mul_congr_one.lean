-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KmCover.mul_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.975293+00:00
-- url     : https://prove2.me/submissions/2c9929ae-8950-446b-aa0a-009596c408ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SolveUnitriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KmCover
open Matrix
variable {R : Type*} [CommRing R] {n : ℕ}
namespace GlobalTheory.CompanionTheory.KmCover
theorem _root_.solution {J : Ideal R} {a b : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J)
    (hb : ∀ i j, b i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) :
    ∀ i j, (a * b) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J := by
  intro i j
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  have e2 : (a * b) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
      ((a - 1) * (b - 1)) i j + (a i j - (1 : Matrix (Fin n) (Fin n) R) i j) +
        (b i j - (1 : Matrix (Fin n) (Fin n) R) i j) := by
    rw [← Matrix.sub_apply, e]
    rfl
  rw [e2]
  refine J.add_mem (J.add_mem ?_ (ha i j)) (hb i j)
  rw [Matrix.mul_apply]
  exact J.sum_mem fun k _ => J.mul_mem_right _ (ha i k)
end GlobalTheory.CompanionTheory.KmCover
