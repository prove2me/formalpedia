-- Prove2me | solution 1 for GlobalTheory.MultisetOfProduct.eval_prod_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:43.556653+00:00
-- url     : https://prove2.me/submissions/f918f6c5-ba0d-4220-a012-2277b68ec96c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetEqOfProdAddEq

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
theorem _root_.solution (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]
end GlobalTheory.MultisetOfProduct
