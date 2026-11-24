-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSSmLin.ex_mem_UJset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:14.50509+00:00
-- url     : https://prove2.me/submissions/f4216e04-9dc0-4855-8e9f-10d304cd863e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
import Theorems.Thm_Formalism_REAL_exp_indefinite_unitary_holds


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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    ex X t ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t
end GlobalTheory.CompanionTheory.DSSmLin
