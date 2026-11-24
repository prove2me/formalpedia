-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.abs_emain_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:43.995815+00:00
-- url     : https://prove2.me/submissions/2fd43899-33ea-4c03-b452-b6749646b2b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_li_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution {θ : ℤ} {β u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hβ1 : β ≤ 1)
    (hu : 4 ≤ u) : |Emain θ β u| ≤ 3 * u := by
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ u by linarith) hβ1
  have h2 : 2 ≤ u ^ β := by
    have h3 : u ^ (1 / 2 : ℝ) ≤ u ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e : (2 : ℝ) ≤ u ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; linarith
    linarith
  obtain ⟨a1, a2⟩ := li_bounds (x := u) (by linarith)
  obtain ⟨b1, b2⟩ := li_bounds h2
  unfold Emain
  rw [abs_le]
  rcases hθ with rfl | rfl | rfl <;> push_cast <;> constructor <;> linarith
end GlobalTheory.Lin.PsiToPi
