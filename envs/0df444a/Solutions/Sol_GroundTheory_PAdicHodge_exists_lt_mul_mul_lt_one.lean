-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_lt_mul_mul_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:18.625254+00:00
-- url     : https://prove2.me/submissions/b8642358-ca1f-4394-b661-dbad051dd63e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
namespace GroundTheory.PAdicHodge
theorem _root_.solution {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ q < s * s * s := by
  refine ⟨(3 + q) / 4, by linarith, by linarith, ?_⟩
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 27 - 10 * q - q * q := by nlinarith
  nlinarith [mul_pos h1 h2]
end GroundTheory.PAdicHodge
