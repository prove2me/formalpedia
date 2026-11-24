-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmBracket.lie_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:54.132285+00:00
-- url     : https://prove2.me/submissions/56b0b2b8-46ef-4528-873a-8f9294e7b54a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.SmBracket
theorem _root_.solution {J X Y : Mat n} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0 := by
  have hLX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * J = J * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * J = J * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel
end GlobalTheory.CompanionTheory.SmBracket
