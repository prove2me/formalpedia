-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolCoef.isOpen_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:18.128064+00:00
-- url     : https://prove2.me/submissions/a70a3c62-a8c8-4d07-9c10-43ad25c86b0e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolCoef
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.HolCoef
theorem _root_.solution : IsOpen cone :=
  isOpen_ne_fun ((continuous_apply (4 : Fin (2 * 0 + 4 + 1))).comp (continuous_apply (4 : Fin (2 * 0 + 4 + 1)))) continuous_const
end GlobalTheory.CompanionTheory.HolCoef
