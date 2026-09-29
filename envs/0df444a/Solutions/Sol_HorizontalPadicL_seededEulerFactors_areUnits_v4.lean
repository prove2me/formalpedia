-- Prove2me | solution 1 for HorizontalPadicL.seededEulerFactors_areUnits_v4
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:58:20.416288+00:00
-- url     : https://prove2.me/submissions/18a293ae-8716-4717-a810-733c789c7003

import Definitions.Def_KN_InverseSeedConventionV2
import Theorems.Thm_HorizontalPadicL_horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
import Definitions.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (Θ : SeededFiniteThetaDataV3 L) :
    Θ.HasUnitEulerFactors := by
  intro A n
  rcases Θ with ⟨R, hR, hintegral, characters, theta, eulerFactor, haug⟩
  subst R
  apply horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2 L.exponent A
  calc
    ‖((horizontalAugmentation (eulerFactor A n) :
        (𝓞_ℂ_[p]).toSubring) : ℂ_[p])‖ =
        ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) -
          (η.2 (L.primeAt n)) ^ 2 - f.epsilon (L.primeAt n))‖ := haug A n
    _ = 1 := (L.primeAt_orderly n).2.2.2
