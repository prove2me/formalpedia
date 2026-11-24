-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_unit_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:15.497731+00:00
-- url     : https://prove2.me/submissions/acf7c0ab-f240-4667-9ac2-44e28e6fd923

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_diagonal_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_isUnit_det_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_rowOp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_colOp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_colOp_mul_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mul_rowOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution {s : Finset ι} {k : ι}
    (ih : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι)
    {A : Matrix ι ι R} (hA : IsUnit A.det) (hF : Fixed (insert k s) A)
    (hk : k ∉ s) (hu : IsUnit (A k k)) : A ∈ elem R ι := by
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set v : ι → R := fun i => if i = k then 0 else -(A i k * ui) with hv
  set x : ι → R := fun j => if j = k then 0 else -(ui * A k j) with hx
  set D : ι → R := Function.update (fun _ => 1) k ui with hD
  have hDu : ∀ i, IsUnit (D i) := by
    intro i
    by_cases h : i = k
    · subst h
      simp only [hD, Function.update_self]
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hui)
    · simp [hD, Function.update_of_ne h]
  have hCm := colOp_mem k v (by simp [hv])
  have hRm := rowOp_mem k x (by simp [hx])
  have hDm := diagonal_mem hDu
  set A4 : Matrix ι ι R := Matrix.diagonal D * ((colOp k v * A) * rowOp k x) with hA4
  have entry : ∀ i j, A4 i j = D i * ((A i j + v i * A k j) +
      (A i k + v i * A k k) * x j) := by
    intro i j
    rw [hA4, Matrix.diagonal_mul, mul_rowOp_apply, colOp_mul_apply, colOp_mul_apply]
  have hF4 : Fixed s A4 := by
    intro i j hij
    rw [entry]
    by_cases hi : i = k
    · subst hi
      by_cases hj : j = i
      · subst hj
        simp [hv, hx, hD, Matrix.one_apply]
        rw [mul_comm]; exact hui
      · have : A i i * ui = 1 := hui
        simp only [hv, hx, if_true, hj, if_false, hD, Function.update_self,
          Matrix.one_apply, Ne.symm hj]
        linear_combination (-(ui * A i j)) * this
    · by_cases hj : j = k
      · subst hj
        simp [hv, hx, hi, hD, Function.update_of_ne hi, Matrix.one_apply]
        have : A j j * ui = 1 := hui
        linear_combination (-A i j) * this
      · have hDi : D i = 1 := by simp [hD, Function.update_of_ne hi]
        have hvx : (A i k + v i * A k k) = 0 := by
          have : A k k * ui = 1 := hui
          simp only [hv, hi, if_false]
          linear_combination (-A i k) * this
        rw [hDi, hvx, zero_mul, add_zero, one_mul]
        rcases hij with h | h
        · have hi' : i ∉ insert k s := by simp [hi, h]
          have h0 : A i k = 0 := by
            rw [hF i k (Or.inl hi'), Matrix.one_apply_ne hi]
          rw [hF i j (Or.inl hi')]
          simp [hv, hi, h0]
        · have hj' : j ∉ insert k s := by simp [hj, h]
          have h0 : A k j = 0 := by
            rw [hF k j (Or.inr hj'), Matrix.one_apply_ne (Ne.symm hj)]
          rw [hF i j (Or.inr hj'), h0, mul_zero, add_zero]
  have hdet : IsUnit A4.det := by
    rw [hA4, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact (isUnit_det_of_mem hDm).mul
      (((isUnit_det_of_mem hCm).mul hA).mul (isUnit_det_of_mem hRm))
  have h4 := ih A4 hdet hF4
  exact mem_of_mul_left hCm (mem_of_mul_right hRm (mem_of_mul_left hDm h4))
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
