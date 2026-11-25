-- Prove2me | solution 1 for GroundTheory.Brauer.degree_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:18.308397+00:00
-- url     : https://prove2.me/submissions/2104b65f-abfe-4de3-8c8a-7bfdb9863b98

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
theorem _root_.solution [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (n : ℕ) :
    degree K A = n ↔ finrank K A = n ^ 2 := by
  rw [finrank_eq_degree_sq K A]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Nat.pow_left_injective two_ne_zero h⟩
end GroundTheory.Brauer
