-- Prove2me | solution 1 for GlobalTheory.HeckeIdealValue.onId_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:49.041953+00:00
-- url     : https://prove2.me/submissions/a72e0596-1141-49c0-a0f5-ca2a3526b459

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
theorem _root_.solution (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId ((v.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v, FractionalIdeal.count_self, zpow_one]
  intro w hw
  rw [FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), zpow_zero]
end GlobalTheory.HeckeIdealValue
