-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bes.torusDiag_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:47.074087+00:00
-- url     : https://prove2.me/submissions/887a66bc-cc6a-43de-9c5d-70ce13170d72

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusTail_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bes
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
namespace GlobalTheory.CompanionTheory.Bes
theorem _root_.solution (k : ℕ) {r : ℕ} (c : Fin r → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : torusDiag k c i = 1 := by
  unfold torusDiag
  rw [if_pos h2, torusTail_ge c h1]
end GlobalTheory.CompanionTheory.Bes
