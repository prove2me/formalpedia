-- Prove2me | solution 1 for GlobalTheory.LaurentFrac.prod_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:40:02.609018+00:00
-- url     : https://prove2.me/submissions/e18778ab-a13b-4daf-acb5-484e42b71da4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdZpowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFrac
namespace GlobalTheory.LaurentFrac
theorem _root_.solution {K : Type} [Field K] {I : Type} [Fintype I] (a : I → K) (N : I → ℤ)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, a i ^ N i) * ∏ i, a i ^ (-N i).toNat = ∏ i, a i ^ (N i).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ha i)]
  congr 1
  omega
end GlobalTheory.LaurentFrac
