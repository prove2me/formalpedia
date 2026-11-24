-- Prove2me | solution 1 for GlobalTheory.MinorNorm.deriv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:39:05.953346+00:00
-- url     : https://prove2.me/submissions/8e0c41de-7e13-4271-b3d3-54bfadb33952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_deriv_prod

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
namespace GlobalTheory.MinorNorm
theorem _root_.solution {m : ℕ} (D : Derivation ℂ R R) (M : Matrix (Fin m) (Fin m) R) :
    D M.det = ∑ t, (M.updateRow t fun u => D (M t u)).det := by
  have key : ∀ N : Matrix (Fin m) (Fin m) R,
      N.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl
  simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, D.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    deriv_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, smul_eq_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]
end GlobalTheory.MinorNorm
