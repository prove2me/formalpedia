-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_multiset_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:32:35.417994+00:00
-- url     : https://prove2.me/submissions/3d63dc9d-4d3b-4928-ab88-fa1c54ea32df

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
omit [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (s : Multiset E) : ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, norm_mul, ih, Multiset.map_cons, Multiset.prod_cons]
end GroundTheory.PAdicHodge
