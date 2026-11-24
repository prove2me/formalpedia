-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ech_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:47.147456+00:00
-- url     : https://prove2.me/submissions/8424cf19-ebe0-4d35-a92f-22b982fb766e

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
theorem _root_.solution {α : Type} (s : Finset α) (f : α → ℚ) : ech (∑ a ∈ s, f a) = ∏ a ∈ s, ech (f a) := by
  unfold ech
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
end GlobalTheory.SW.FourierJ
