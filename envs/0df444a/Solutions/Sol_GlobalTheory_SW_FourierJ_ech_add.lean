-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ech_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:41.299223+00:00
-- url     : https://prove2.me/submissions/8d1bc5c3-849b-43f7-804b-161e32c54faf

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
theorem _root_.solution (s t : ℚ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
end GlobalTheory.SW.FourierJ
