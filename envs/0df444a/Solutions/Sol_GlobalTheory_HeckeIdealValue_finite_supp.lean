-- Prove2me | solution 1 for GlobalTheory.HeckeIdealValue.finite_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:46.640233+00:00
-- url     : https://prove2.me/submissions/e2b5b50c-ff8a-44bf-a33b-adc15412fe14

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
theorem _root_.solution (χ : HChar L) (J : FractionalIdeal (𝓞 L)⁰ L) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v J).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun v hv h => hv ?_
  simp [h]
end GlobalTheory.HeckeIdealValue
