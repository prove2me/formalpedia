-- Prove2me | solution 1 for GlobalTheory.DoublingSeries.exists_cpow_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:43.324987+00:00
-- url     : https://prove2.me/submissions/b608e421-7ab9-46d3-850e-fc416266bdb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries
namespace GlobalTheory.DoublingSeries
theorem _root_.solution {q : ℕ} (hq : 1 < q) (s₀ : ℝ) {z : ℂ} (hz : z ≠ 0) (hzs : ‖z‖ < (q : ℝ) ^ (-s₀)) :
    ∃ s : ℂ, s₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 < Real.log q := Real.log_pos hq1
  refine ⟨-Complex.log z / (Real.log q : ℂ), ?_, ?_⟩
  · have e : (-Complex.log z / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [e, lt_div_iff₀ hl]
    have := Real.log_lt_log (norm_pos_iff.2 hz) hzs
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    have hl' : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
    rw [show (Real.log q : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz
end GlobalTheory.DoublingSeries
