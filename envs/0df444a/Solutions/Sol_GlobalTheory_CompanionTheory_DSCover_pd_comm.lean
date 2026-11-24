-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.pd_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:30.623269+00:00
-- url     : https://prove2.me/submissions/de8103c1-e705-47f2-8870-db02136739a3

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_pd_apply
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
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (i j : σ) : pd i * pd j = pd j * pd i := by
  classical
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, pd_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, add_comm]
end GlobalTheory.CompanionTheory.DSCover
