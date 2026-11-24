-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.norm_ech
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:47.249144+00:00
-- url     : https://prove2.me/submissions/08264142-cffc-4af5-a480-991e49583f0a

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
theorem _root_.solution (t : ℚ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _
end GlobalTheory.SW.FourierJ
