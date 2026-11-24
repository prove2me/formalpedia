-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolCoef.rdV_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:41.807381+00:00
-- url     : https://prove2.me/submissions/44336da4-7150-4b59-9945-3ff7309e5786

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolCoef_hasDerivAt_exp_real

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
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CompanionTheory.HolCoef
theorem _root_.solution (X g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : RdV X f g = fderiv ℂ f g (g * X) := by
  unfold RdV
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := (LinearMap.mulLeft ℝ g).toContinuousLinearMap
  have h1 : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_real X)
  have h2 : HasFDerivAt f ((fderiv ℂ f g).restrictScalars ℝ) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    rw [Matrix.mul_one]
    exact hf.hasFDerivAt.restrictScalars ℝ
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
end GlobalTheory.CompanionTheory.HolCoef
