-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSVerma.dd_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:31.638802+00:00
-- url     : https://prove2.me/submissions/e3f829ad-f0a2-4d84-9d15-c86bdd0c3e6a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_DSVerma_pderiv_comm__b92bf3ad3e4e
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
open MvPolynomial
namespace GlobalTheory.CompanionTheory.DSVerma
theorem _root_.solution (a b c d : Fin n) : Commute (dd ε a b) (dd ε c d) := by
  unfold dd
  split_ifs
  · refine LinearMap.ext fun f => ?_
    exact pderiv_comm' _ _ f
  all_goals simp
end GlobalTheory.CompanionTheory.DSVerma
