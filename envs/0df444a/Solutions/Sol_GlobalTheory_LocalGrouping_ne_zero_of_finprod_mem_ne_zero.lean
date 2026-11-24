-- Prove2me | solution 1 for GlobalTheory.LocalGrouping.ne_zero_of_finprod_mem_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:02.884851+00:00
-- url     : https://prove2.me/submissions/5cf38e23-6326-40aa-9c65-26f3e15df670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.LocalGrouping
open Function
namespace GlobalTheory.LocalGrouping
theorem _root_.solution {ι : Type} (S : Set ι) (h : ι → ℂ)
    (hf : (mulSupport h).Finite) (hne : ∏ᶠ i ∈ S, h i ≠ 0) : ∀ i ∈ S, h i ≠ 0 := by
  intro i hi hzero
  apply hne
  have hfin : (S ∩ mulSupport h).Finite := hf.subset Set.inter_subset_right
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
  apply Finset.prod_eq_zero (i := i)
  · simp [Set.Finite.mem_toFinset, hi, Function.mem_mulSupport, hzero]
  · exact hzero
end GlobalTheory.LocalGrouping
