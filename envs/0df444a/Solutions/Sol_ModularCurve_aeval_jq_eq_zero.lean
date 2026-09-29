-- Prove2me | solution 1 for ModularCurve.aeval_jq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f457ae50-edbf-5862-b501-c5254443a6dd

import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_aeval_jq_eq_zero

open ModularCurve IntermediateField

noncomputable section

theorem solution {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0 :=by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (Polynomial.aeval jq p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single n]
    · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
        mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_of_lt,
        mul_zero]
      omega
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

end

end S_ModularCurve_aeval_jq_eq_zero
end P2MW
export P2MW.S_ModularCurve_aeval_jq_eq_zero (solution)
