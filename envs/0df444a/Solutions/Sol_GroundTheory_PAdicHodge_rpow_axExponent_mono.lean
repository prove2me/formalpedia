-- Prove2me | solution 1 for GroundTheory.PAdicHodge.rpow_axExponent_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:13.218932+00:00
-- url     : https://prove2.me/submissions/80da094b-92ae-4846-8617-8c35c5c2e656

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast
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
theorem _root_.solution {j k : ℕ} (h : j ≤ k) :
    (p : ℝ) ^ axExponent p j ≤ (p : ℝ) ^ axExponent p k :=
  Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_mono h)
end GroundTheory.PAdicHodge
