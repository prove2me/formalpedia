-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.riemannTheta_half_add_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:08.285007+00:00
-- url     : https://prove2.me/submissions/45946cd3-5544-47fe-a375-8ecb58c5bb39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution (α β : ℤ) (z τ : ℂ) :
    riemannTheta (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) !![τ] ![z + τ] =
      (-1) ^ β * cexp (-π * I * τ - 2 * π * I * z) *
        riemannTheta (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) !![τ] ![z] := by
  have hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have := riemannTheta_add_mulVec_intCast hs (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) ![z]
    (fun _ => 1)
  have e : (![z] + !![τ] *ᵥ fun _ => ((1 : ℤ) : ℂ)) = ![z + τ] := by
    funext i
    fin_cases i
    simp [mulVec, dotProduct]
  rw [← e, this]
  congr 1
  have : ((-1 : ℂ)) ^ β = cexp ((β : ℂ) * -(π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  rw [this, ← Complex.exp_add]
  congr 1
  simp [mulVec, dotProduct]
  ring
end GlobalTheory.RiemannThetaModel
