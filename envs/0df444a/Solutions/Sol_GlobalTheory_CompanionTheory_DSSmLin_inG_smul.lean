-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSSmLin.inG_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:04.048049+00:00
-- url     : https://prove2.me/submissions/226d1599-4c0a-47b0-bf87-fd14ce027515

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    inG ε ((s : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
    ← smul_add, hX, smul_zero]
end GlobalTheory.CompanionTheory.DSSmLin
