-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.ext_of_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:09:32.240565+00:00
-- url     : https://prove2.me/submissions/710bb077-88e7-4e54-a572-b1d51be71fa6

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_pairA_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_algebraMap_eq_pairA
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_denseRange_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]
end GlobalTheory.CompanionTheory.AdeleCharLocal
