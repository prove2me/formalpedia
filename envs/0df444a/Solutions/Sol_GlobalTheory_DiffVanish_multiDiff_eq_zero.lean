-- Prove2me | solution 1 for GlobalTheory.DiffVanish.multiDiff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:12.636544+00:00
-- url     : https://prove2.me/submissions/513aeff5-90aa-46b1-9d88-8f2792999cf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
namespace DiffVanish
theorem _root_.solution {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    {ι : Type*} [Fintype ι] (hn : n ≤ Fintype.card ι) (g : ι → G) : multiDiff g φ = 0 := by
  rw [multiDiff_eq_shiftAct]
  exact h.shiftAct_eq_zero (Ideal.pow_le_pow_right hn (prod_diffElt_mem univ g))
end DiffVanish
end GlobalTheory
