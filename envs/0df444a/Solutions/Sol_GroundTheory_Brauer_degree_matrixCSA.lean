-- Prove2me | solution 1 for GroundTheory.Brauer.degree_matrixCSA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:44.162602+00:00
-- url     : https://prove2.me/submissions/07af605b-76c0-4804-ab6d-2efdd2a73b46

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_degree_matrix

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
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    degree K (matrixCSA A n) = n * degree K A := by
  have h := degree_matrix K A (Fin n)
  rw [Fintype.card_fin] at h
  exact h
end GroundTheory.Brauer
