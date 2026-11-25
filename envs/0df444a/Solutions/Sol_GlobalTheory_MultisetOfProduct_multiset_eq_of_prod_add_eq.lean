-- Prove2me | solution 1 for GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:49.919669+00:00
-- url     : https://prove2.me/submissions/1752c929-98ba-4ff1-ba84-06660395830b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetEqOfProdAddEq
import Theorems.Thm_GlobalTheory_MultisetOfProduct_eval_prod_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultisetOfProduct
open Polynomial
namespace GlobalTheory.MultisetOfProduct
theorem _root_.solution {m m' : Multiset ℂ}
    (h : ∀ (u : ℂ), Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m)
      = Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m')) : m = m' := by

  have hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod =
      ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_neg, eval_prod_neg]
    exact h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
end GlobalTheory.MultisetOfProduct
