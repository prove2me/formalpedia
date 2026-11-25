-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_eq_of_aeval_minpoly_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:03.350477+00:00
-- url     : https://prove2.me/submissions/e2717d4b-22a8-4e35-b419-7a587caca315

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace

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
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {y r : PadicAlgCl p}
    (h : aeval r (minpoly ℚ_[p] y) = 0) : ‖r‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic y) h]
end GroundTheory.PAdicHodge
