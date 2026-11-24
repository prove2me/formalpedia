-- Prove2me | solution 1 for GlobalTheory.RiemannRel.differentiableOn_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:05.49213+00:00
-- url     : https://prove2.me/submissions/1f1e2d89-0583-457c-90b3-a244cb76042f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Theorems.Thm_GlobalTheory_RiemannRel_differentiableOn_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {B : Set V}
    (A h : V → Matrix (Fin g) (Fin g) ℂ) (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hh : ∀ b ∈ B, h b * A b = 1) (i j : Fin g) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ b ∈ B, (A b).det ≠ 0 := fun b hb hz => by
    have := congrArg Matrix.det (hh b hb)
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hinv : ∀ b ∈ B, h b i j = ((A b).det)⁻¹ * (A b).adjugate i j := fun b hb => by
    rw [(Matrix.inv_eq_left_inv (hh b hb)).symm, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
  refine DifferentiableOn.congr ?_ hinv
  refine ((_root_.GlobalTheory.RiemannRel.differentiableOn_det A hA).inv hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  refine _root_.GlobalTheory.RiemannRel.differentiableOn_det _ fun k l => ?_
  by_cases hk : k = j
  · subst hk; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne hk]; exact hA k l
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
