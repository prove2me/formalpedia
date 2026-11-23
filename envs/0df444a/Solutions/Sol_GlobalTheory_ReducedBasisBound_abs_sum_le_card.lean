-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.abs_sum_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:25.860062+00:00
-- url     : https://prove2.me/submissions/59909204-8992-472a-a17b-811152a9ec77

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
theorem _root_.solution {N : ℕ} (f : Fin N → ℝ) (B : ℝ) (h : ∀ p, |f p| ≤ B) :
    |∑ p, f p| ≤ N * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |f p| ≤ ∑ _p : Fin N, B := Finset.sum_le_sum (fun p _ => h p)
    _ = N * B := by simp
end GlobalTheory.ReducedBasisBound
