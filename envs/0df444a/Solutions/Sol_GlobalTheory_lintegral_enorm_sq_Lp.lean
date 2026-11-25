-- Prove2me | solution 1 for GlobalTheory.lintegral_enorm_sq_Lp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:37.045331+00:00
-- url     : https://prove2.me/submissions/2cbf906a-2186-4042-86b2-1b4e10f99c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtendAeLinearOfLocalSqBoundDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm
end GlobalTheory
