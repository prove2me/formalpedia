-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.UJ_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.572037+00:00
-- url     : https://prove2.me/submissions/a9847fa3-2123-4df8-afb5-cf377a1a383f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_UJ_left_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε :=
  inv_eq_left_inv (UJ_left_inv hg)
end GlobalTheory.CompanionTheory.SmoothModule
