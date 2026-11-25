-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKExp.kExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:51:14.76968+00:00
-- url     : https://prove2.me/submissions/73ab99ce-880f-4200-9ec7-15a1467311f6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KExp
import Theorems.Thm_Formalism_REAL_compact_exponential_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKExp
namespace GlobalTheory.CompanionTheory.DSICKExp
theorem _root_.solution : CompanionTheory.D.DSIC.KExp := by
  intro n ε g hg
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.compact_exponential_surjective n ε g hg
  exact ⟨Y, hY, he.symm⟩
end GlobalTheory.CompanionTheory.DSICKExp
