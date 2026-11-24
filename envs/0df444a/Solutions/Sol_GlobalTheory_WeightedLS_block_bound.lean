-- Prove2me | solution 1 for GlobalTheory.WeightedLS.block_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:42.468663+00:00
-- url     : https://prove2.me/submissions/bb6d3b04-a603-4761-8d3e-659e9e9d87ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}
namespace GlobalTheory.WeightedLS
theorem _root_.solution (A : Matrix (Fin g) (Fin g) ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : Fin g → ℝ) (k : Fin g),
      |A.det * (A.updateCol k c).det| ≤ K * ‖c‖ * (A.det * A.det) := by
  by_cases hA : A.det = 0
  · exact ⟨0, le_rfl, fun c k => by simp [hA]⟩
  · let f : (Fin g → ℝ) →L[ℝ] (Fin g → ℝ) := LinearMap.toContinuousLinearMap (Matrix.cramer A)
    have hp : 0 < |A.det| := abs_pos.mpr hA
    refine ⟨‖f‖ / |A.det|, by positivity, fun c k => ?_⟩
    have h1 : |(A.updateCol k c).det| ≤ ‖f‖ * ‖c‖ := by
      have h2 : (A.updateCol k c).det = f c k := by
        simp [f, Matrix.cramer_apply]
      rw [h2]
      exact (norm_le_pi_norm (f c) k).trans (f.le_opNorm c)
    rw [abs_mul, ← abs_mul_abs_self A.det]
    calc |A.det| * |(A.updateCol k c).det| ≤ |A.det| * (‖f‖ * ‖c‖) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = _ := by field_simp
end GlobalTheory.WeightedLS
