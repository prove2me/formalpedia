-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.conj_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:18.464001+00:00
-- url     : https://prove2.me/submissions/85f13341-688b-4b2c-a818-179b78a4edd0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
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
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution (g h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    g * single a b 1 * h = ∑ c, ∑ d, (g c a * h b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [matrix_eq_sum_single (g * single a b 1 * h)]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  rw [smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, single_apply, ite_and]
end GlobalTheory.CompanionTheory.SmoothModule
