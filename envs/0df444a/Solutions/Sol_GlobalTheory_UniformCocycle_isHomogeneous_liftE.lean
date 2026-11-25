-- Prove2me | solution 1 for GlobalTheory.UniformCocycle.isHomogeneous_liftE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:03.896373+00:00
-- url     : https://prove2.me/submissions/484c4bc8-5dca-4508-8266-bc6222649dca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
import Theorems.Thm_GlobalTheory_UniformCocycle_liftCoeff_zero
import Theorems.Thm_GlobalTheory_UniformCocycle_coeff_liftE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformCocycle
variable {R : Type} [CommRing R] {σ : Type}
namespace GlobalTheory.UniformCocycle
theorem _root_.solution {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]
end GlobalTheory.UniformCocycle
