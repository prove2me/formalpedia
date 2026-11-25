-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.CongOne.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:49.315801+00:00
-- url     : https://prove2.me/submissions/6093beec-f012-4d42-94c1-e725a18e4d3f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HeckeMult
namespace CongOne
theorem _root_.solution {n : ℕ} {I : Ideal R} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : CongOne I X) (hY : CongOne I Y) : CongOne I (X * Y) := by
  intro i j
  have h : (X * Y) i j - (1 : Matrix (Fin n) (Fin n) R) i j
      = ((X - 1) * Y) i j + (Y i j - (1 : Matrix (Fin n) (Fin n) R) i j) := by
    have h0 : X * Y - 1 = (X - 1) * Y + (Y - 1) := by noncomm_ring
    have h1 := congrFun (congrFun h0 i) j
    simpa using h1
  rw [h]
  refine I.add_mem ?_ (hY i j)
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (by simpa using hX i k)
end CongOne
end GlobalTheory.CompanionTheory.HeckeMult
