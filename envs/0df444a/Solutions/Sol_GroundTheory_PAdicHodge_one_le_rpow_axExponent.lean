-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_le_rpow_axExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:19.271063+00:00
-- url     : https://prove2.me/submissions/c5e21e5a-c911-4ad7-8128-47c134768561

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast
import Theorems.Thm_GroundTheory_PAdicHodge_axExponent_nonneg

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
theorem _root_.solution (k : ℕ) : 1 ≤ (p : ℝ) ^ axExponent p k :=
  Real.one_le_rpow one_lt_prime_cast.le (axExponent_nonneg k)
end GroundTheory.PAdicHodge
