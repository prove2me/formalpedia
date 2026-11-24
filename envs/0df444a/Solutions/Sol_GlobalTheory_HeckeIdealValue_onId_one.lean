-- Prove2me | solution 1 for GlobalTheory.HeckeIdealValue.onId_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:47.873022+00:00
-- url     : https://prove2.me/submissions/26d9745b-4b34-4963-a32b-32f51139a89f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeIdealValue
open Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
namespace GlobalTheory.HeckeIdealValue
theorem _root_.solution (χ : HChar L) : χ.onId (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]
end GlobalTheory.HeckeIdealValue
