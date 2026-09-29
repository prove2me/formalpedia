-- Prove2me | solution 1 for ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d558f67b-6452-5bda-8693-e53a9ebbf9f1

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero
import Theorems.Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff (n : ℤ) =
      (6 : L)⁻¹ * ∑ md ∈ Nat.divisorsAntidiagonal n,
          ((md.2 : ℕ) : L) ^ 3 *
            ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) +
              (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) +
        (if N ∣ n then (240 / 144 : L) * ((Nat.divisors (n / N)).sum fun d => ((d : ℕ) : L) ^ 3) else 0) := by
  by_cases hv1 : v 1 = 0
  · exact ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero L N ξ hξ v hv hv1 n hn
  · exact ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero L N ξ hξ v hv hv1 n hn

end S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq
end P2MW
export P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq (solution)
