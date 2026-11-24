-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSHighestOfKType.height_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:13.194801+00:00
-- url     : https://prove2.me/submissions/1760b9be-5b23-47ac-9521-b60055e220c0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSHighestOfKType
theorem _root_.solution (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
end GlobalTheory.CompanionTheory.DSHighestOfKType
