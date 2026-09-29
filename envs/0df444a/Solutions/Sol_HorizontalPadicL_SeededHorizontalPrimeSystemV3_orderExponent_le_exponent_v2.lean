-- Prove2me | solution 1 for HorizontalPadicL.SeededHorizontalPrimeSystemV3.orderExponent_le_exponent_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:18.216222+00:00
-- url     : https://prove2.me/submissions/55c68323-5c7e-4b2b-ac9c-6ddec2629132

import Definitions.Def_KN_InverseSeedConventionV2
import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B) :
    ∀ n, L.orderExponent ≤ L.exponent n := by
  intro n
  unfold SeededHorizontalPrimeSystemV3.exponent
  rw [← Nat.pow_dvd_iff_le_padicValNat (Fact.out : p.Prime).ne_one]
  exact ((L.primeAt_orderly n).2.1.symm).dvd'
  exact Nat.sub_ne_zero_iff_lt.mpr (L.primeAt_prime n).one_lt

end HorizontalPadicL
