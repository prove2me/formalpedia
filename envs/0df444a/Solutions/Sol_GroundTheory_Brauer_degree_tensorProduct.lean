-- Prove2me | solution 1 for GroundTheory.Brauer.degree_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:21.196799+00:00
-- url     : https://prove2.me/submissions/0e1f4f9f-56e4-4f4b-8ad8-17e6ca05e18e

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_finrank_eq_degree_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open Module TensorProduct
universe u v w
variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
namespace GroundTheory.Brauer
theorem _root_.solution [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (B : Type w) [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B] :
    degree K (A ⊗[K] B) = degree K A * degree K B := by
  rw [degree, Module.finrank_tensorProduct, finrank_eq_degree_sq K A, finrank_eq_degree_sq K B,
    ← mul_pow, Nat.sqrt_eq']
end GroundTheory.Brauer
