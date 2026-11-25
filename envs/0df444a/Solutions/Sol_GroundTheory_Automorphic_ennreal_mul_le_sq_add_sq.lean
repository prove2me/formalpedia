-- Prove2me | solution 1 for GroundTheory.Automorphic.ennreal_mul_le_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:59.809801+00:00
-- url     : https://prove2.me/submissions/cfabbad7-2b27-431b-bd44-5ac49358e9af

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
namespace GroundTheory.Automorphic
theorem _root_.solution (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add
end GroundTheory.Automorphic
