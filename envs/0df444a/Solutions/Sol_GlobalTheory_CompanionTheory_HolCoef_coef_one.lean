-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolCoef.coef_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:15.528085+00:00
-- url     : https://prove2.me/submissions/c9cbccd5-c0fb-4f82-9fc5-5cd22868d5c0

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
theorem _root_.solution (p N : ℕ) : coef p N 1 = 1 := by
  have h2 : minor2 1 = 1 := by
    unfold minor2; rw [Matrix.submatrix_one _ (by decide), det_one]
  have h3 : minor3 1 = 1 := by
    unfold minor3; rw [Matrix.submatrix_one _ (by decide), det_one]
  have h4 : minor4 1 = 1 := by
    unfold minor4; rw [Matrix.submatrix_one _ (by decide), det_one]
  simp [coef, h2, h3, h4]
end GlobalTheory.CompanionTheory.HolCoef
