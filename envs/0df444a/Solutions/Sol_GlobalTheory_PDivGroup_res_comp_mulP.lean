-- Prove2me | solution 1 for GlobalTheory.PDivGroup.res_comp_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:08.632565+00:00
-- url     : https://prove2.me/submissions/f0317589-b27a-4432-9d65-31ae13679704

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (G : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) : (G.res n).comp (G.mulP n) = mulBy O _ p :=
  BialgHom.ext (G.res_mulP n)
end GlobalTheory.PDivGroup
