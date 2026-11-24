-- Prove2me | solution 1 for GlobalTheory.idempotent_eq_of_basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:34.070379+00:00
-- url     : https://prove2.me/submissions/7fbecb08-927c-4fe9-b8e3-8267ddebc561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Theorems.Thm_GlobalTheory_idem_germ_eq_of_isUnit_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by
  intro X e e' he he' hb
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' (fun x hx => ?_)
  change X.presheaf.germ ⊤ x hx e = X.presheaf.germ ⊤ x hx e'
  apply idem_germ_eq_of_isUnit_iff (R := X.presheaf.stalk x)
  · rw [← map_mul, he]
  · rw [← map_mul, he']
  · rw [← X.mem_basicOpen e x hx, ← X.mem_basicOpen e' x hx, hb]
end GlobalTheory
