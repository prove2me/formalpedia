-- Prove2me | solution 1 for NgoFL.transfer_factor_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T18:21:38.109067+00:00
-- url     : https://prove2.me/submissions/b147fc95-c4cb-4fc0-97dd-bd0cc51f294b

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant
import Theorems.Thm_NgoFL_discriminant_eq_subDiscriminant_mul_resultant_sq

open NgoFL

/-- **Ngô, 1.11.3**: applying an additive valuation to the identity
`D_G = ± D_H · (R^G_H)^2` of 1.10.3 gives `v(D_G) = v(D_H) + 2 v(R^G_H)`. -/
theorem solution {ι M N F : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [Fintype ι] [DecidableEq ι] (P : RootPairing ι F M N)
    (v : AddValuation F (WithTop ℤ)) (s L : Finset ι) (hL : IsHalfSystem P sᶜ L) (x : N) :
    v (discriminant P x) = v (subDiscriminant P s x) + 2 • v (resultant P L x) := by
  rw [discriminant_eq_subDiscriminant_mul_resultant_sq P s L hL x]
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_neg, AddValuation.map_one]
  simp
