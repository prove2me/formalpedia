-- Prove2me | solution 1 for GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:30.891891+00:00
-- url     : https://prove2.me/submissions/c500dda7-30b6-46b9-b8db-bba60fd51899

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPiUpperHalfPlaneImBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPiUpperHalfPlaneImBoundsStatement
import Theorems.Thm_GlobalTheory_isCompact_pi_upperHalfPlane_im_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  first | exact @GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | exact GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | (intros; apply GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds <;> assumption)
end _root_.GlobalTheory.T
