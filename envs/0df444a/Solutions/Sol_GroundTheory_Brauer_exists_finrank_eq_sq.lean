-- Prove2me | solution 1 for GroundTheory.Brauer.exists_finrank_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:29.575643+00:00
-- url     : https://prove2.me/submissions/1ec82369-c833-42cd-b839-353f8516183d

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_exists_algEquiv_matrix_algebraicClosure

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
    ∃ n : ℕ, finrank K A = n ^ 2 :=
  let ⟨n, _, h, _⟩ := exists_algEquiv_matrix_algebraicClosure K A
  ⟨n, h⟩
end GroundTheory.Brauer
