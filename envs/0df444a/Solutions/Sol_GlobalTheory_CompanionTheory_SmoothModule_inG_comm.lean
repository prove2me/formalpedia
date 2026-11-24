-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.inG_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:33.771517+00:00
-- url     : https://prove2.me/submissions/24f3a851-6fd9-4af2-94e1-ce09ea31f135

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_theta_mul

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
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X * Y - Y * X) := by
  rw [inG_iff] at *; rw [theta_sub, theta_mul, theta_mul, hX, hY]; abel
end GlobalTheory.CompanionTheory.SmoothModule
