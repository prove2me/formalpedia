-- Prove2me | solution 1 for MTT.Eigenform.p_mem_coefficientPrime
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T10:34:26.075996+00:00
-- url     : https://prove2.me/submissions/06aabbbb-346c-4a50-a1f5-d82d9ecd08fc

import Definitions.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

open NumberField

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (p : 𝓞 f.coefficientField) ∈ f.coefficientPrime ιp := by
  rw [f.mem_coefficientPrime_iff ιp]
  have hp := Padic.norm_p_lt_one (p := p)
  have hext : ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
    simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  simpa using hext.trans_lt hp
