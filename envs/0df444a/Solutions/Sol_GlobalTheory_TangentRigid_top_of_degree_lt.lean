-- Prove2me | solution 1 for GlobalTheory.TangentRigid.top_of_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:30.719067+00:00
-- url     : https://prove2.me/submissions/36ce4a21-83cb-4751-9ad9-5ed8ba6de4c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}
namespace GlobalTheory.TangentRigid
theorem _root_.solution (h : p.degree < (d : WithBot ℕ)) : Top p d 0 :=
  ⟨natDegree_le_of_degree_le h.le, coeff_eq_zero_of_degree_lt h⟩
end GlobalTheory.TangentRigid
