-- Prove2me | solution 1 for GlobalTheory.WittSolve.smod_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:25.277674+00:00
-- url     : https://prove2.me/submissions/c14c2533-6093-49c3-95df-9bc3b7f5896b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]
namespace GlobalTheory.WittSolve
theorem _root_.solution (x y : WittVector p R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(p : WittVector p R)}) ^ n •
      (⊤ : Submodule (WittVector p R) (WittVector p R))] ↔ (p : WittVector p R) ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]
end GlobalTheory.WittSolve
