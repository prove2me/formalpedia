-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.nrm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:40.937838+00:00
-- url     : https://prove2.me/submissions/8314d1d0-d721-453a-8ab8-6e422bcc4104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.PartialZetaSum
theorem _root_.solution (𝔟 : Frac F) : 0 ≤ nrm 𝔟 := by
  unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
end GlobalTheory.PartialZetaSum
