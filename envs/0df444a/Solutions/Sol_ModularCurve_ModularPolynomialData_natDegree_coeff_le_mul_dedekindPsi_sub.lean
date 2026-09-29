-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c45007de-7080-51f3-bf26-f533435baf44

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_coeff_coeff_swapBivar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve Polynomial

theorem solution (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p)
    (hsymm : EvalSymm data.Φ) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ p * (dedekindPsi p - i) := by
  have hψ : dedekindPsi p = p + 1 := by
    unfold dedekindPsi
    rw [hp.out.divisors, Finset.filter_insert, if_pos squarefree_one,
        Finset.filter_singleton, if_pos hp.out.squarefree,
        Finset.sum_insert (Finset.notMem_singleton.mpr hp.out.one_lt.ne),
        Finset.sum_singleton, Nat.div_self hp.out.pos, Nat.div_one]
  have hdeg := data.natDegree_eq
  have hmon := data.monic
  have hswap := swapBivar_eq_of_evalSymm hsymm
  have hcoeff : ∀ a b, (data.Φ.coeff a).coeff b = (data.Φ.coeff b).coeff a := fun a b => by
    conv_lhs => rw [← hswap]
    exact coeff_coeff_swapBivar data.Φ b a
  have hweak := ModularPolynomialData.natDegree_coeff_le p data

  have hlead : data.Φ.coeff (p + 1) = 1 := by
    rw [← hψ, ← hdeg]; exact hmon.coeff_natDegree
  rw [hψ]
  rcases le_or_gt i (p + 1) with hi | hi
  · rcases Nat.lt_or_ge i p with hip | hip
    ·
      calc (data.Φ.coeff i).natDegree
          ≤ p + 1 := hweak i
        _ ≤ p * 2 := by omega
        _ ≤ p * (p + 1 - i) := Nat.mul_le_mul_left p (by omega)
    · rcases (show p = i ∨ p + 1 = i by omega) with rfl | rfl
      ·
        simp only [Nat.add_sub_cancel_left, Nat.mul_one]
        have hp1 : (data.Φ.coeff p).coeff (p + 1) = 0 := by
          rw [hcoeff p (p + 1), hlead, Polynomial.coeff_one,
            if_neg hp.out.ne_zero]

        refine Nat.le_of_lt_succ (lt_of_le_of_ne (hweak p) ?_)
        intro heq
        have hz : data.Φ.coeff p = 0 :=
          Polynomial.leadingCoeff_eq_zero.mp
            (show (data.Φ.coeff p).coeff (data.Φ.coeff p).natDegree = 0 by rw [heq]; exact hp1)
        rw [hz, Polynomial.natDegree_zero] at heq; omega
      ·
        simp [hlead]
  ·
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hψ ▸ hi)]

end S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub (solution)
