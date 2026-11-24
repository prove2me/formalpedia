-- Prove2me | solution 1 for GlobalTheory.QNorm.adeleOn_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:40.265581+00:00
-- url     : https://prove2.me/submissions/fc7709ba-3ea4-4cf5-b203-f654daff646d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
import Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_mem
import Theorems.Thm_GlobalTheory_QNorm_adeleOn_snd_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]
end GlobalTheory.QNorm
