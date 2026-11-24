-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSChainAdj.sg_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:24.863011+00:00
-- url     : https://prove2.me/submissions/ef78d9df-e94e-402f-be2d-bcbc56138e8d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSChainAdj
theorem _root_.solution (i : NC ε) (A : Finset (NC ε)) : sg i (insert i A) = sg i A := by
  unfold sg
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]
end GlobalTheory.CompanionTheory.DSChainAdj
