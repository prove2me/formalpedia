-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bes.torus_col_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:33.854698+00:00
-- url     : https://prove2.me/submissions/ee8d404d-4c08-48a0-9cbc-0270c2caf233

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter

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
theorem _root_.solution {k r : ℕ} {d e : Fin (2 * r + k + 1) → ℂ} (hde : ∀ i, d i * e i = 1)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : col k r m) :
    col k r (Matrix.diagonal d * m * Matrix.diagonal e) := by
  intro i j hj hi
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hm i j hj hi]
  split_ifs with h
  · subst h
    rw [mul_one, hde]
  · simp
end GlobalTheory.CompanionTheory.Bes
