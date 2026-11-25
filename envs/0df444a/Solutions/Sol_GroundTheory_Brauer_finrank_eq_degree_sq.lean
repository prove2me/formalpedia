-- Prove2me | solution 1 for GroundTheory.Brauer.finrank_eq_degree_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:53.774814+00:00
-- url     : https://prove2.me/submissions/5a1b5f8a-a67c-4d6d-92b3-00f816224d01

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_exists_finrank_eq_sq

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
theorem _root_.solution [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    finrank K A = degree K A ^ 2 := by
  obtain ⟨n, h⟩ := exists_finrank_eq_sq K A
  rw [degree, h, Nat.sqrt_eq']
end GroundTheory.Brauer
