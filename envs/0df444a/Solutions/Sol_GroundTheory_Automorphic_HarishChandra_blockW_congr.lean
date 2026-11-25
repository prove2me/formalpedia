-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.blockW_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:59.273614+00:00
-- url     : https://prove2.me/submissions/257ef00a-b661-4599-b23c-e478f8d3c1a1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {l : List (Fin n × Fin n)} {m m' : Fin n × Fin n →₀ ℕ}
    (h : ∀ a ∈ l, m a = m' a) : blockW l m = blockW l m' := by
  unfold blockW
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
end GroundTheory.Automorphic.HarishChandra
