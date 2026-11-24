-- Prove2me | solution 1 for GlobalTheory.MinorNorm.del_addCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:01.187948+00:00
-- url     : https://prove2.me/submissions/3c86dbf0-7958-49d3-a94e-a12cb5e8b528

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_addCol_exp

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
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
variable {σ : Type} (v : Fin l → Fin l → σ)
namespace GlobalTheory.MinorNorm
theorem _root_.solution {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) :
    del v (addCol a K) = minor v K * del v a := by
  unfold del
  simp only [addCol_exp ha, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]
  ring
end GlobalTheory.MinorNorm
