-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleIdeal.count_idealOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:04:51.694893+00:00
-- url     : https://prove2.me/submissions/b218b897-e074-4822-8709-f866c7f4cad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_ordAt_eventually
import Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_finite_pow
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleIdeal
theorem _root_.solution (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (idealOf y : FractionalIdeal (𝓞 E)⁰ E) = ordAt y w := by
  have h1 : (idealOf y : FractionalIdeal (𝓞 E)⁰ E) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (ordAt y v : ℤ) := by
    have := map_finprod (FractionalIdeal.coeIdealHom (𝓞 E)⁰ E) (finite_pow y)
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply] at this
    simp only [zpow_natCast]
    exact this
  rw [h1, FractionalIdeal.count_finprod]
  filter_upwards [ordAt_eventually y] with v hv
  simp [hv]
end GlobalTheory.CMVal.IdeleIdeal
