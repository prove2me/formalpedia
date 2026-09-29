-- Prove2me | solution 1 for HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9248ead8-a50a-58a9-a798-28397ba270ff

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm

set_option autoImplicit false

open scoped MatrixGroups

open HeckeEis MvPolynomial in
theorem solution {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    MvPolynomial.coeff (Finsupp.single 1 n) P = MvPolynomial.eval ![0, 1] P := by
  classical
  have hhom : P.IsHomogeneous n := (mem_homogeneousSubmodule n P).mp hP
  rw [MvPolynomial.eval_eq]
  symm
  rw [Finset.sum_eq_single (Finsupp.single 1 n)]
  · simp [Finsupp.single_apply]
  · intro d hd hne

    have hdn : d.degree = n := by
      by_contra hc
      exact (mem_support_iff.mp hd) (hhom.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
    have hd0 : d 0 ≠ 0 := by
      intro h0
      apply hne
      ext i
      fin_cases i
      · simpa using h0
      · simp
        omega
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hd0) (by simp [zero_pow hd0]), mul_zero]
  · intro hn
    rw [MvPolynomial.notMem_support_iff.mp hn, zero_mul]

end S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
end P2MW
export P2MW.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm (solution)
