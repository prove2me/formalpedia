-- Prove2me | solution 1 for GlobalTheory.IwaFlag.sesq_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:32.87675+00:00
-- url     : https://prove2.me/submissions/c2989cfc-ac68-4a68-98b8-321532e0897c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
open Matrix
namespace GlobalTheory.IwaFlag
theorem _root_.solution {n p q : ℕ} (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin n) (Fin q) R)
    (i : Fin p) (j : Fin q) : sesq c G (fun k => A k i) (fun k => B k j) = ((B.map c)ᵀ * (G * A)) j i := by
  simp only [sesq, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]
end GlobalTheory.IwaFlag
