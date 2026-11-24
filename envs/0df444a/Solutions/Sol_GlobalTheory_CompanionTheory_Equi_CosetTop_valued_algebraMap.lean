-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetTop.valued_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:49.679944+00:00
-- url     : https://prove2.me/submissions/aa31b0e4-6cc1-456b-a6df-aea8b986e015

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetTop
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
end GlobalTheory.CompanionTheory.Equi.CosetTop
