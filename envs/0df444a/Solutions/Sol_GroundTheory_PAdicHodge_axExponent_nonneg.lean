-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axExponent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:39.372849+00:00
-- url     : https://prove2.me/submissions/6ad10b84-e7de-4d5d-9cf6-7e5bbbefd84d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_axExponent_zero
import Theorems.Thm_GroundTheory_PAdicHodge_axExponent_mono

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
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : ℕ) : 0 ≤ axExponent p k := by
  rw [← axExponent_zero (p := p)]
  exact axExponent_mono (Nat.zero_le k)
end GroundTheory.PAdicHodge
