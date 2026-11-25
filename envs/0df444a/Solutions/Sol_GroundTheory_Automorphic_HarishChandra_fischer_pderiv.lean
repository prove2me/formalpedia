-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:11.40705+00:00
-- url     : https://prove2.me/submissions/5173f583-6b3d-400b-a757-531d20c07cb2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_conj_symm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_X_mul

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
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (pderiv a f) g = fischer f (X a * g) := by
  rw [← fischer_conj_symm, ← fischer_X_mul, fischer_conj_symm]
end GroundTheory.Automorphic.HarishChandra
