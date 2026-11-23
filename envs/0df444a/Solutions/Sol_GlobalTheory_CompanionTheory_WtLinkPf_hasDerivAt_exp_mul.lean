-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.hasDerivAt_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:01.763485+00:00
-- url     : https://prove2.me/submissions/7abc90ed-df64-4174-9218-4ac86624f623

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
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
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) (Complex.exp ((s : ℂ) * c) * c) s := by
  have := ((hasDerivAt_id s).ofReal_comp.mul_const c).cexp
  simpa using this
end GlobalTheory.CompanionTheory.WtLinkPf
