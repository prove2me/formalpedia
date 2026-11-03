-- Prove2me | solution 1 for OAI.Laughlin.Fock.truncatedQuadratic_error_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:33:25.000821+00:00
-- url     : https://prove2.me/submissions/42d870cb-c223-4f58-b664-bc07d28fa716

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_truncatedScalingInv_coordinate_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators InnerProductSpace

theorem quadratic_perturbation_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : ι → ι → ℝ) (x : ι → F) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, |R i j| ≤ ε) :
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
      ε * (Fintype.card ι : ℝ) * ∑ i, ‖x i‖^2 := by
  have hp (i j : ι) :
      |R i j * ⟪x i, x j⟫_ℝ| ≤ ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
    rw [abs_mul]
    have hi : |⟪x i, x j⟫_ℝ| ≤ (‖x i‖^2 + ‖x j‖^2)/2 := by
      have hc := abs_real_inner_le_norm (x i) (x j)
      nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
    calc
      |R i j| * |⟪x i, x j⟫_ℝ| ≤ ε * ((‖x i‖^2 + ‖x j‖^2)/2) :=
        mul_le_mul (hR i j) hi (abs_nonneg _) hε
      _ = _ := by ring
  calc
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
        ∑ i, ∑ j, |R i j * ⟪x i, x j⟫_ℝ| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : ι, ∑ j : ι, ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [mul_add, add_div, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring_nf
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupation_coefficient_perturbation {I : Type*} [Fintype I] (Q : ℕ)
    (R : Finset (Fin (Q+1)) → I → I → ℝ) (v : I → Space Q)
    (ε : ℝ) (hε : 0 ≤ ε) (hR : ∀ A i j, |R A i j| ≤ ε) :
    |∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j, R A i j *
      ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  calc
    _ ≤ ∑ A : Finset (Fin (Q+1)), |∑ i, ∑ j, R A i j *
        ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : Finset (Fin (Q+1)), ε * (Fintype.card I : ℝ) *
        ∑ i, ‖(occupationBasis Q).repr (v i) A‖^2 :=
      Finset.sum_le_sum (fun A hA => quadratic_perturbation_bound (R A)
        (fun i => (occupationBasis Q).repr (v i) A) ε hε (hR A))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedMetricPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupationQuadratic_coordinates {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (v : I → Space Q) :
    occupationQuadratic Q R v = ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
      R i j * ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
  simp only [occupationQuadratic,occupationInner,Finset.mul_sum,Complex.re_sum,
    Complex.inner,Complex.star_def]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A hA
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem truncatedQuadratic_error_s50_oai {I : Type*} [Fintype I] (L Q : ℕ)
    (R S : I → I → ℝ) (v : I → Space Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ A : Finset (Fin (Q+1)), ∀ i j,
      |((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j| ≤ ε) :
    |occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  have he : occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v =
      ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
        (((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j) *
          ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
    rw [occupationQuadratic_coordinates,occupationQuadratic_coordinates,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro A hA
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j hj
    rw [truncatedScalingInv_coordinate_s50,truncatedScalingInv_coordinate_s50]
    simp only [Complex.inner,map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    ring
  rw [he]
  exact occupation_coefficient_perturbation Q _ v ε hε hR

end Laughlin.Fock

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Fock.truncatedQuadratic_error_s50_oai.{u_1} := @OAI.Laughlin.Fock.truncatedQuadratic_error_s50_oai.{u_1}
