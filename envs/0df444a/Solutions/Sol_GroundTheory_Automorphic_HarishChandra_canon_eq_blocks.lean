-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_eq_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:36.126462+00:00
-- url     : https://prove2.me/submissions/f6eb3296-cbf2-48a3-a3c8-0ad8ec0c5638

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) :
    canon m = word (blockW (lowL n) m) * word (blockW (diagL n) m) * word (blockW (upL n) m) := by
  rw [canon, expand_eq_blocks, word_append, word_append]
end GroundTheory.Automorphic.HarishChandra
