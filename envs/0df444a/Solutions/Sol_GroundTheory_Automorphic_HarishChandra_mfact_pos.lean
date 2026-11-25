-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mfact_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:38.705871+00:00
-- url     : https://prove2.me/submissions/86ba3959-539e-4833-b3cc-10d6ebf21388

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm

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
theorem _root_.solution (m : σ →₀ ℕ) : 0 < mfact m :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _
end GroundTheory.Automorphic.HarishChandra
