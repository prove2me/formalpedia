-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.pd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:36.63316+00:00
-- url     : https://prove2.me/submissions/2d56aa73-4d96-4337-ad20-987b2dc80e6f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (i : σ) (f : MvPolynomial σ ℂ) : pd i f = pderiv i f := rfl
end GlobalTheory.CompanionTheory.DSCover
