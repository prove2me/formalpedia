-- Prove2me | solution 1 for MTT.Eigenform.coefficientPrime_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T10:41:34.416896+00:00
-- url     : https://prove2.me/submissions/d75ffd3d-fe76-43b7-8d3f-9103bed14839

import Definitions.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := by
  rw [MTT.Eigenform.coefficientPrime]
  let _ := (IsLocalRing.maximalIdeal.isMaximal (𝓞_ℂ_[p])).isPrime
  exact Ideal.IsPrime.comap _
