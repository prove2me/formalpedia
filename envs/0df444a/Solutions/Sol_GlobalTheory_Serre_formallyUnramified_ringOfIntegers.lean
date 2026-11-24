-- Prove2me | solution 1 for GlobalTheory.Serre.formallyUnramified_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:39.799363+00:00
-- url     : https://prove2.me/submissions/41e3b8d1-50a0-4162-9c47-568e6de23102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
import Theorems.Thm_GlobalTheory_Serre_ringOfIntegers_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
open NumberField
variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
namespace GlobalTheory.Serre
theorem _root_.solution [Algebra (𝓞 K) k] :
    Algebra.FormallyUnramified k (k ⊗[𝓞 K] 𝓞 E) := by
  have hinj := ringOfIntegers_injective k K (algebraMap (𝓞 K) k)
  let : Algebra K k := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (𝓞 K) K k :=
    .of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap hinj x).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors (𝓞 K))) E :=
    IsIntegralClosure.isLocalization (𝓞 K) K E (𝓞 E)
  have : Algebra.IsPushout (𝓞 K) K (𝓞 E) E :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 E) E).symm
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  have : Algebra.FormallyUnramified K (K ⊗[𝓞 K] 𝓞 E) :=
    .of_equiv (Algebra.IsPushout.equiv (𝓞 K) K (𝓞 E) E).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange (𝓞 K) K k k (𝓞 E))
end GlobalTheory.Serre
