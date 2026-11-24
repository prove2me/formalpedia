-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSSmLin.inG_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:02.971373+00:00
-- url     : https://prove2.me/submissions/91eedbf6-541b-4e80-bf42-88c4deb8bf11

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSSmLin
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.DSSmLin
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
end GlobalTheory.CompanionTheory.DSSmLin
