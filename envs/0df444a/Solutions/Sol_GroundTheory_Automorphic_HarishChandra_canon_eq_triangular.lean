-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_eq_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:41.324119+00:00
-- url     : https://prove2.me/submissions/3f72f539-57a0-47b6-b15d-232e87482315

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_blockW_diagL

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
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) :
    canon m = word (blockW (lowL n) m) * hcEmb (monomial (diagExp m) 1) *
      word (blockW (upL n) m) := by
  rw [canon_eq_blocks, word_blockW_diagL]
end GroundTheory.Automorphic.HarishChandra
