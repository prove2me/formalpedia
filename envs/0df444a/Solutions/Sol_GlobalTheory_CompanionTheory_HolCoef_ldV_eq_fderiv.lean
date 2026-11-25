-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolCoef.ldV_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:43.245298+00:00
-- url     : https://prove2.me/submissions/5408a728-7e1b-4b8e-9533-769a3cc64787

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
theorem _root_.solution {k r : ℕ} (X g : B.Mat k r) (f : B.Mat k r → E)
    (hf : DifferentiableAt ℂ f g) : B.LdV X f g = fderiv ℂ f g (-(X * g)) := by
  unfold B.LdV
  let L : B.Mat k r →L[ℝ] B.Mat k r := (LinearMap.mulRight ℝ g).toContinuousLinearMap
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) * g) ((-X) * g) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_real (-X))
  have h2 : HasFDerivAt f ((fderiv ℂ f g).restrictScalars ℝ) (NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * g) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    rw [Matrix.one_mul]
    exact hf.hasFDerivAt.restrictScalars ℝ
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
  simp only [smul_neg, Matrix.neg_mul] at h3
  exact h3
end GlobalTheory.CompanionTheory.HolCoef
