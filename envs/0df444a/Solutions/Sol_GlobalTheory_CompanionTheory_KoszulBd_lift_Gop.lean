-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.lift_Gop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:28.728831+00:00
-- url     : https://prove2.me/submissions/5172e6fa-5304-4dea-8246-5a889bedd4b0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_ann
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_cre

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (T : Module.End ℂ V) (c d : Fin n) :
    Commute (Gop ε c d) (lift ε T : Module.End ℂ (Ch ε V)) := by
  unfold Gop
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
  exact ((lift_cre T i).symm.mul_left (lift_ann T j).symm).smul_left _
end GlobalTheory.CompanionTheory.KoszulBd
