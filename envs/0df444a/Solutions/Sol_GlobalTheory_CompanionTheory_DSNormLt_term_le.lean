-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:20.88534+00:00
-- url     : https://prove2.me/submissions/527d34e2-61fa-46c7-86a7-81336d7c65c7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution {s z : ℝ} (hs : |s| ≤ 1) : s * z ≤ |z| := by
  calc s * z ≤ |s * z| := le_abs_self _
    _ = |s| * |z| := abs_mul _ _
    _ ≤ 1 * |z| := by gcongr
    _ = |z| := one_mul _
end GlobalTheory.CompanionTheory.DSNormLt
