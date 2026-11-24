-- Prove2me | solution 1 for GlobalTheory.Wick.contraction_rename_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:48.643855+00:00
-- url     : https://prove2.me/submissions/0503b196-fb1c-4eab-ad4a-3dcb8e0ee614

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_contraction_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]
namespace GlobalTheory.Wick
theorem _root_.solution (γ : ι → κ → R) (q : MvPolynomial κ R) :
    contraction γ (rename Sum.inr q) = 0 := by
  classical
  rw [contraction_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_pderiv_comm, pderiv_eq_zero_of_notMem_vars (i := Sum.inl i), map_zero, smul_zero]
  intro h
  obtain ⟨j, -, hj⟩ := mem_vars_rename _ _ h
  cases hj
end GlobalTheory.Wick
