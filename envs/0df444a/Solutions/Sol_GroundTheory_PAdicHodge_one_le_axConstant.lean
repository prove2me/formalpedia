-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_le_axConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:25.160018+00:00
-- url     : https://prove2.me/submissions/368c7800-95fa-4c1b-9702-a4fe4fc029d9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast

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
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution : 1 ≤ axConstant p :=
  Real.one_le_rpow one_lt_prime_cast.le (div_nonneg (by linarith [one_lt_prime_cast (p := p)])
    (sq_nonneg _))
end GroundTheory.PAdicHodge
