-- Prove2me | solution 1 for GlobalTheory.MinorNorm.det_eq_sum_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:37.361978+00:00
-- url     : https://prove2.me/submissions/007a6e23-b026-4fa7-ae6d-40d457115148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_cast_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (x : Fin k → Fin k → R) :
    (Matrix.of x).det = ∑ ρ : Fin k → Fin k, (eps ρ : R) * ∏ t, x (ρ t) t := by
  conv_lhs => rw [← Matrix.one_mul (Matrix.of x)]
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [cast_eps, ← det_transpose, det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  simp [Matrix.one_apply, eq_comm]
end GlobalTheory.MinorNorm
