-- Prove2me | solution 1 for Lagrange.interpolate_eq_of_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:56.537467+00:00
-- url     : https://prove2.me/submissions/ddfb44a1-3117-456b-bc1d-c401b572b0dd

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
namespace Lagrange
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
  (S : Finset F) (f : F → F) (Q : Polynomial F)
  (h_deg : Q.degree < S.card)
  (h_agree : ∀ x ∈ S, Q.eval x = f x) :
  Lagrange.interpolate S id f = Q := by
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq S ?_ h_deg ?_
  · exact Lagrange.degree_interpolate_lt f (Set.injOn_id _)
  · intro x hx
    conv_lhs => rw [show x = id x from rfl]
    rw [Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hx, ← h_agree x hx]
end Lagrange
