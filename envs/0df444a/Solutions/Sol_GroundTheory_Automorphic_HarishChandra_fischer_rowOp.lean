-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_rowOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:16.686377+00:00
-- url     : https://prove2.me/submissions/3b7b7d5e-845a-4455-b0aa-a3ddc4a1db7e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_X_mul
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_pderiv
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_sum_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_sum_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (i j : Fin n) (f g : Poly n) :
    fischer (rowOp i j f) g = fischer f (rowOp j i g) := by
  rw [rowOp_apply, rowOp_apply, fischer_sum_left, fischer_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fischer_X_mul, fischer_pderiv]
end GroundTheory.Automorphic.HarishChandra
