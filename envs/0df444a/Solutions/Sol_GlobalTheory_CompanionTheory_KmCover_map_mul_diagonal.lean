-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KmCover.map_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:14.975322+00:00
-- url     : https://prove2.me/submissions/7443cec8-6859-4a1e-81b0-7ee5bc30aa22

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
namespace GlobalTheory.CompanionTheory.KmCover
theorem _root_.solution {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (e : Fin n → K) (X Y : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f (X i j) * e j = e i * f (Y i j)) :
    X.map f * Matrix.diagonal e = Matrix.diagonal e * Y.map f := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact h i j
end GlobalTheory.CompanionTheory.KmCover
