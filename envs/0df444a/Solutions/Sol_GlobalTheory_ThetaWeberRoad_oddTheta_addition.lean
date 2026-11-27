-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_addition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:37:56.633801+00:00
-- url     : https://prove2.me/submissions/0451525d-1443-42ef-90df-769edb5f791b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
open scoped Real
noncomputable section
namespace GlobalTheory.ThetaWeberRoad
private theorem g_add_mul_g_sub_of_addition_laws (E g σ : ℂ → ℂ) (c Δ z w : ℂ)
    (hE : E (z + w) * E (z - w) = E z ^ 2 * E w ^ 2) (hz : E z ≠ 0) (hw : E w ≠ 0)
    (hI : ∀ u, E u * g u = c * σ u) (hσ : σ (z + w) * σ (z - w) = -(σ z ^ 2 * σ w ^ 2 * Δ)) :
    c ^ 2 * (g (z + w) * g (z - w)) = -(g z ^ 2 * g w ^ 2 * Δ) := by
  have h0 : E z ^ 2 * E w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hw)
  apply mul_left_cancel₀ h0
  have h1 := hI (z + w)
  have h2 := hI (z - w)
  have h3 := hI z
  have h4 := hI w
  calc E z ^ 2 * E w ^ 2 * (c ^ 2 * (g (z + w) * g (z - w)))
      = c ^ 2 * ((E (z + w) * g (z + w)) * (E (z - w) * g (z - w))) := by rw [← hE]; ring
    _ = c ^ 4 * (σ (z + w) * σ (z - w)) := by rw [h1, h2]; ring
    _ = -((c * σ z) ^ 2 * (c * σ w) ^ 2 * Δ) := by rw [hσ]; ring
    _ = -((E z * g z) ^ 2 * (E w * g w) ^ 2 * Δ) := by rw [h3, h4]
    _ = E z ^ 2 * E w ^ 2 * -(g z ^ 2 * g w ^ 2 * Δ) := by ring
end GlobalTheory.ThetaWeberRoad
end
end

set_option autoImplicit false
open Complex
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution (hSA : Formalism.L2.Th1.F.SgStarAdd) (τ : UpperHalfPlane)
    (hI : ∀ z : ℂ, Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * oddTheta τ z =
      deriv (oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z)
    (z w : ℂ) (hz : z ∉ (GlobalTheory.periodPairOfTau τ).lattice) (hw : w ∉ (GlobalTheory.periodPairOfTau τ).lattice) :
    deriv (oddTheta τ) 0 ^ 2 * (oddTheta τ (z + w) * oddTheta τ (z - w)) =
      -(oddTheta τ z ^ 2 * oddTheta τ w ^ 2 *
        (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ z - GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ w)) := by
  have hσ := hSA (GlobalTheory.periodPairOfTau τ) z w hz hw
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp
  refine g_add_mul_g_sub_of_addition_laws (fun u => Complex.exp ((Real.pi : ℂ) * u ^ 2 / (2 * ((τ.im : ℝ) : ℂ))))
    (oddTheta τ) (Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ)) _ _ z w ?_ (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _) hI hσ
  simp only [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
end GlobalTheory.ThetaWeberRoad
