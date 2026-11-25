-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.ph_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:51.845871+00:00
-- url     : https://prove2.me/submissions/75d3d8ca-147e-47f6-98ea-10a429575b3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
theorem _root_.solution (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) (la : Set.Ioi (0 : ℝ)) :
    0 ≤ ph f rd q R₀ la := by
  unfold ph
  split_ifs
  · positivity
  · exact le_rfl
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
