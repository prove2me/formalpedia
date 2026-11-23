-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.ann_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:25.542134+00:00
-- url     : https://prove2.me/submissions/e2ad2369-13c5-47e1-81bd-980538b1cae9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl
end GlobalTheory.CompanionTheory.ChainCAR
