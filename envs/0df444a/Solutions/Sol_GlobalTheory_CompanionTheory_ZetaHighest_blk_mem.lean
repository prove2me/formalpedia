-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.blk_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:30.710554+00:00
-- url     : https://prove2.me/submissions/795d1b26-35be-4df5-8b5e-98cad73b731f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 h).2
end GlobalTheory.CompanionTheory.ZetaHighest
