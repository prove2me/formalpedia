-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:35.695494+00:00
-- url     : https://prove2.me/submissions/3a620813-24d9-4ff2-a1af-7542eb7c00c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution {N : ℕ} (a : Fin N → ℝ) (n Z P : Matrix (Fin N) (Fin N) ℝ)
    (h : diagonal a * n * P = Z * diagonal a * n) (p j : Fin N) :
    a p * (n * P) p j = ∑ q, Z p q * a q * n q j := by
  have := congrFun (congrFun h p) j
  rw [Matrix.mul_assoc, diagonal_mul] at this
  rw [this, Matrix.mul_apply]
  simp [mul_diagonal]
end GlobalTheory.ReducedBasisBound
