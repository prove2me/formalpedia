-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.star_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:01.979578+00:00
-- url     : https://prove2.me/submissions/e9b297ad-7341-483d-8278-a2a042731633

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
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp
end GlobalTheory.CompanionTheory.WtLinkPf
