-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.cre_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.435684+00:00
-- url     : https://prove2.me/submissions/2157e3dd-c7ae-45de-993a-9710a6b29218

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
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl
end GlobalTheory.CompanionTheory.ChainCAR
