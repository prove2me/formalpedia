-- Prove2me | solution 1 for ModularCurve.dedekindPsi_eq_prod_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/dcadef72-3c4d-5026-8d79-d7088a3c99da

import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_eq_prod_primeFactors
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

open ModularCurve

theorem solution (N : ℕ) (hN : N ≠ 0) :
    dedekindPsi N = ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1) := by
  have hmult := Nat.multiplicative_factorization dedekindPsi
    (fun x y h => ModularCurve.dedekindPsi_mul_of_coprime x y h) dedekindPsi_one hN
  rw [hmult, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : N.factorization p ≠ 0 :=
    (hpp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)).ne'
  rw [ModularCurve.dedekindPsi_prime_pow p _ hpp hk]
  obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [hk', Nat.succ_sub_one, pow_succ]
  ring

end S_ModularCurve_dedekindPsi_eq_prod_primeFactors
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_eq_prod_primeFactors (solution)
