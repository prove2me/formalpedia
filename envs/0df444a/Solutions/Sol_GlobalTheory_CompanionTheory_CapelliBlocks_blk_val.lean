-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.blk_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:23.949493+00:00
-- url     : https://prove2.me/submissions/fece21fc-5cf8-4626-a2d8-421ad19dd41b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (k : Fin (nb ε s)) : ε (blk ε s k) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl k
  exact (Finset.mem_filter.mp this).2
end GlobalTheory.CompanionTheory.CapelliBlocks
