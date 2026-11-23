-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.dl_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.207676+00:00
-- url     : https://prove2.me/submissions/3f14baa3-32ba-4c9a-a26e-a4615f573a0b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (x y : Fin n) : dl x y = dl y x := by
  simp only [dl, eq_comm]
end GlobalTheory.CompanionTheory.DSICFRel
