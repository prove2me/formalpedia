-- Prove2me | solution 1 for N25.Endgame.FBaseCoeffMap25_frobenius_prime
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:04.730199+00:00
-- url     : https://prove2.me/submissions/dc7de1ac-96fc-4014-9a87-c88a15cc4525

import Definitions.Def_N25_CoefficientMap

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

theorem _root_.solution
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [CharP K ℓ] [Algebra (ZMod ℓ) K]
    (f : FBase (ZMod ℓ)) :
    ModularCurve.qExpFrobeniusModL K Γ25 ℓ
        (FBaseCoeffMap25 (ZMod ℓ) K f) =
      FBaseCoeffMap25 (ZMod ℓ) K (f ^ ℓ) := by
  apply Subtype.ext
  change ModularCurve.qExpand K ℓ
      (ModularCurve.coeffMap (algebraMap (ZMod ℓ) K) (f : LaurentSeries (ZMod ℓ))) =
    ModularCurve.coeffMap (algebraMap (ZMod ℓ) K) ((f : LaurentSeries (ZMod ℓ)) ^ ℓ)
  rw [map_pow]
  apply ModularCurve.qExpand_eq_pow_of_coeff_fixed
  intro n
  rw [ModularCurve.coeffMap_coeff, ← map_pow]
  congr 1
  exact ZMod.pow_card _

end N25.Endgame
