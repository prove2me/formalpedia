-- Prove2me | solution 1 for GlobalTheory.cubeSign_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:10:36.87397+00:00
-- url     : https://prove2.me/submissions/d9ee8587-7cc5-4caf-8652-2136532bd9fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι]
theorem _root_.solution (t : Finset ι) (i : ι) : cubeSign t i = 1 ∨ cubeSign t i = -1 := by
  unfold GlobalTheory.cubeSign
  first
    | exact neg_one_pow_eq_or ℤ _
    | (split_ifs <;> simp)

