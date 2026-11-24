-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.conj_ech
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:05.683363+00:00
-- url     : https://prove2.me/submissions/9c9335ad-6a51-4ddf-b05f-18a366958098

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
theorem _root_.solution (t : ℚ) : conj (ech t) = ech (-t) := by
  unfold ech
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
  push_cast
  ring
end GlobalTheory.SW.FourierJ
