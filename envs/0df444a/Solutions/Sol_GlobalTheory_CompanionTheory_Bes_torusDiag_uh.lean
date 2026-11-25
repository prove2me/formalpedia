-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bes.torusDiag_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:59:26.716978+00:00
-- url     : https://prove2.me/submissions/64a7b488-151d-4294-99f6-be9d5777b84d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_tau
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row


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
theorem _root_.solution (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    Matrix.diagonal (torusDiag k c) ∈ UH (Hpk k r) := by
  show (Matrix.diagonal (torusDiag k c))ᴴ * Hpk k r * Matrix.diagonal (torusDiag k c) = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, hpk_row]
  split_ifs with h
  · subst h
    have := torusDiag_tau k hc i
    simp only [Pi.star_apply]
    linear_combination (sgn k r i) * this
  · simp
end GlobalTheory.CompanionTheory.Bes
