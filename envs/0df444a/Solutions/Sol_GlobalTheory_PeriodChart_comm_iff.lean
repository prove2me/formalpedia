-- Prove2me | solution 1 for GlobalTheory.PeriodChart.comm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:29.065477+00:00
-- url     : https://prove2.me/submissions/bd408355-dbe1-4305-83fc-012ffcd78a7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
omit [IsCMField E]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (ty ty' : Fin g → (E →+* ℂ)) (W : Matrix (Fin g) (Fin g) ℂ) :
    (∀ a, dg ty a * W = W * dg ty' a) ↔ ∀ i j, ¬ ty i = ty' j → W i j = 0 := by
  constructor
  · intro h i j hij
    by_contra hW
    apply hij
    have key : ∀ a : 𝓞 E, ty i (a : E) = ty' j (a : E) := by
      intro a
      have e := congrFun (congrFun (h a) i) j
      simp only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
      rw [mul_comm (W i j)] at e
      exact mul_right_cancel₀ hW e
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => key a)
  · intro h a
    ext i j
    simp only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : ty i = ty' j
    · rw [hij, mul_comm]
    · rw [h i j hij]; simp
end GlobalTheory.PeriodChart
