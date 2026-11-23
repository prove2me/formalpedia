-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.lift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:25.372178+00:00
-- url     : https://prove2.me/submissions/a49cdbbb-5479-443b-a620-4a839ccd3352

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (S T : Module.End ℂ Z) :
    (lift ε (S * T) : Module.End ℂ (Ch ε Z)) = lift ε S * lift ε T := rfl
end GlobalTheory.CompanionTheory.DSICKoszul
