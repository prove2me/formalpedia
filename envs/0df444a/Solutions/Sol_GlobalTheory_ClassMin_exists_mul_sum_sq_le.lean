-- Prove2me | solution 1 for GlobalTheory.ClassMin.exists_mul_sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:13.243783+00:00
-- url     : https://prove2.me/submissions/b69153a4-a245-4d75-bcdf-f11b6a5d032c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_two_mul_eq_dotProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}
omit [Module.Free ℤ X] [Module.Finite ℤ X]
namespace GlobalTheory.ClassMin
theorem _root_.solution {ι : Type*} [Fintype ι] (hQ : (realExtension Q).PosDef)
    (e : Module.Basis ι ℤ X) : ∃ c > 0, ∀ a, c * ∑ i, (e.repr a i : ℝ) ^ 2 ≤ Q a := by
  obtain ⟨c, hc, h⟩ := posDef_exists_mul_dotProduct_le ((realExtension_posDef_iff Q e).mp hQ)
  refine ⟨c / 2, by positivity, fun a => ?_⟩
  have := h fun i => (e.repr a i : ℝ)
  rw [← two_mul_eq_dotProduct] at this
  simp only [dotProduct, ← pow_two] at this
  linarith
end GlobalTheory.ClassMin
