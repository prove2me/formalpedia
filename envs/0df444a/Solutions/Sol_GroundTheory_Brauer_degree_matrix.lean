-- Prove2me | solution 1 for GroundTheory.Brauer.degree_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:19.556068+00:00
-- url     : https://prove2.me/submissions/07051d65-e575-4159-a59c-8e2b7d3c2e05

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
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    degree K (Matrix ι ι A) = Fintype.card ι * degree K A := by
  rw [degree, Module.finrank_matrix, finrank_eq_degree_sq K A, ← sq, ← mul_pow, Nat.sqrt_eq']
end GroundTheory.Brauer
