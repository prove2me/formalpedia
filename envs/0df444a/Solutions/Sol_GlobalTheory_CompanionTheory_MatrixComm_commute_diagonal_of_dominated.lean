-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixComm.commute_diagonal_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:41.099435+00:00
-- url     : https://prove2.me/submissions/6d417dcc-1cb5-4873-a9a6-b8bc41ef1727

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixComm
namespace GlobalTheory.CompanionTheory.MatrixComm
theorem _root_.solution {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by
  ext i j
  have hij := congrFun (congrFun hZ i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : Z i j = 0
  · simp [hz]
  · have hd : d i = d j := by
      have : Z i j * d i = Z i j * d j := by rw [mul_comm (Z i j) (d i)]; exact hij
      exact mul_left_cancel₀ hz this
    rw [hde i j hd, mul_comm]
end GlobalTheory.CompanionTheory.MatrixComm
