-- Prove2me | solution 1 for GlobalTheory.SW.Vac.om_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:55.283256+00:00
-- url     : https://prove2.me/submissions/9619496d-b08d-47a9-a32f-b0b9f35b78c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    (∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) = pr y.1 y'.2 - pr y'.1 y.2 := by
  simp [pr, Finset.sum_sub_distrib]
end GlobalTheory.SW.Vac
