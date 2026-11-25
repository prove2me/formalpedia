-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ech_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:24.811457+00:00
-- url     : https://prove2.me/submissions/f62bc1cf-1b5d-4b76-b494-aec63608c3b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type}
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution (m : ℤ) : ech (m : ℚ) = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * ((m : ℚ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m
end GlobalTheory.SW.FourierJ
