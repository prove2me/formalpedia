-- Prove2me | solution 1 for GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:31.462227+00:00
-- url     : https://prove2.me/submissions/20987f2a-b9ce-4551-9e7d-baafaa6b8c13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SlopeTestRemainingChoices GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.SlopeTestRemainingChoices.EisFibre
theorem _root_.solution {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
  (Quotient.out β : NzElt 𝔟).2.1
end GlobalTheory.SlopeTestRemainingChoices.EisFibre
