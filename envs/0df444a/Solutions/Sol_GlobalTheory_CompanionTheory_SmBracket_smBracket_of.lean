-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmBracket.smBracket_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:47.779842+00:00
-- url     : https://prove2.me/submissions/b1f8acb6-4037-42d1-aa0f-bf8c5ba33154

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_smBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.SmBracket
theorem _root_.solution : CompanionTheory.D.DSIC.SmLin → CompanionTheory.D.DSIC.SmBracket := fun _ => smBracket
end GlobalTheory.CompanionTheory.SmBracket
