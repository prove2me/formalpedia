-- Prove2me | solution 1 for NumberField.natAbs_discr_le_of_quintic_subfield_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:01.440946+00:00
-- url     : https://prove2.me/submissions/3840c06d-50e2-46be-a295-61d61057925f

import Mathlib
import Theorems.Thm_NumberField_natAbs_discr_le_of_quartic_cyclotomic_tower

set_option autoImplicit false

namespace NumberField

/-- Every quintic subfield of the twenty-fifth cyclotomic field has absolute
discriminant at most `5^8`. -/
theorem _root_.solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsCyclotomicExtension {25} ℚ L]
    (hdegree : Module.finrank ℚ K = 5) :
    (discr K).natAbs ≤ 5 ^ 8 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hL : Module.finrank ℚ L = 20 := by
    rw [IsCyclotomicExtension.Rat.finrank (k := 25) L]
    change Nat.totient (5 ^ 2) = 20
    rw [Nat.totient_prime_pow Nat.prime_five (by decide : 0 < 2)]
    norm_num
  have htower := Module.finrank_mul_finrank ℚ K L
  rw [hdegree, hL] at htower
  have hrelative : Module.finrank K L = 4 := by omega
  have hdiscr : (discr L).natAbs = 5 ^ 35 := by
    haveI : IsCyclotomicExtension {5 ^ 2} ℚ L := by
      norm_num
      infer_instance
    have hd := IsCyclotomicExtension.Rat.discr_prime_pow_succ 5 1 L
    norm_num at hd
    rw [hd]
    norm_num
  exact natAbs_discr_le_of_quartic_cyclotomic_tower K L hrelative hdiscr

end NumberField
