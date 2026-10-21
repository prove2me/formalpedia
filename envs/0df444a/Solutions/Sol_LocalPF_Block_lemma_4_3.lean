-- Prove2me | solution 1 for LocalPF.Block.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T13:29:52.939146+00:00
-- url     : https://prove2.me/submissions/b16bc701-7666-40c4-b81b-88cee3112d2e

import Mathlib
import Definitions.Def_LocalPF_Block_Setting
set_option autoImplicit false
open scoped BigOperators

namespace DobrushinSeries
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma powers_nonneg (C : Matrix I I ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (n : ℕ) (i j : I) : 0 ≤ (C ^ n) i j := by
  induction n generalizing i j with
  | zero => simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hC i k) (ih k j)

lemma weighted_powers (m : I → I → ℝ) (hm_self : ∀ i, m i i = 0)
    (hm_triangle : ∀ i j k, m i k ≤ m i j + m j k)
    (C : Matrix I I ℝ) (hC : ∀ i j, 0 ≤ C i j) (c : ℝ) (hc0 : 0 ≤ c)
    (hCc : ∀ i, ∑ j, Real.exp (m i j) * C i j ≤ c) :
    ∀ n i, ∑ j, Real.exp (m i j) * (C ^ n) i j ≤ c ^ n := by
  intro n
  induction n with
  | zero =>
    intro i
    simp [Matrix.one_apply,hm_self]
  | succ n ih =>
    intro i
    calc
      ∑ j, Real.exp (m i j) * (C ^ (n+1)) i j =
          ∑ k, ∑ j, Real.exp (m i j) * (C i k * (C ^ n) k j) := by
        simp_rw [pow_succ',Matrix.mul_apply,Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ k, ∑ j, (Real.exp (m i k) * C i k) *
          (Real.exp (m k j) * (C ^ n) k j) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro j _
        have he : Real.exp (m i j) ≤ Real.exp (m i k) * Real.exp (m k j) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (hm_triangle i k j)
        calc
          _ ≤ (Real.exp (m i k) * Real.exp (m k j)) * (C i k * (C^n) k j) :=
            mul_le_mul_of_nonneg_right he (mul_nonneg (hC i k) (powers_nonneg C hC n k j))
          _ = _ := by ring
      _ = ∑ k, (Real.exp (m i k) * C i k) *
          (∑ j, Real.exp (m k j) * (C ^ n) k j) := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ k, (Real.exp (m i k) * C i k) * c ^ n := by
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (ih k) (mul_nonneg (Real.exp_pos _).le (hC i k))
      _ = (∑ k, Real.exp (m i k) * C i k) * c ^ n := by rw [Finset.sum_mul]
      _ ≤ c * c ^ n := mul_le_mul_of_nonneg_right (hCc i) (pow_nonneg hc0 n)
      _ = c ^ (n+1) := by rw [pow_succ]; ring

end DobrushinSeries

theorem solution {I : Type*} [Fintype I] [DecidableEq I] (m : I → I → ℝ)
    (hm_self : ∀ i, m i i = 0) (hm_symm : ∀ i j, m i j = m j i)
    (hm_triangle : ∀ i j k, m i k ≤ m i j + m j k)
    (C : Matrix I I ℝ) (hC : ∀ i j, 0 ≤ C i j) (c : ℝ) (hc : c < 1)
    (hCc : ∀ i, ∑ j, Real.exp (m i j) * C i j ≤ c) :
    ∃ D : Matrix I I ℝ, HasSum (fun n : ℕ => C ^ n) D ∧
      (∀ i, ∑ j, Real.exp (m i j) * D i j ≤ 1 / (1 - c)) ∧
      ∀ (i : I) (J : Finset I) (hJ : J.Nonempty),
        ∑ j ∈ J, D i j ≤ Real.exp (-(J.inf' hJ (m i))) / (1 - c) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    refine ⟨0,?_,?_,?_⟩
    · have he : (fun n : ℕ => C^n) = (fun _ => (0 : Matrix I I ℝ)) := by
        funext n
        exact Subsingleton.elim _ _
      rw [he]
      exact hasSum_zero
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i
  | inr hI =>
    let := hI
    have hc0 : 0 ≤ c := (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Real.exp_pos (m (Classical.arbitrary I) j)).le
        (hC (Classical.arbitrary I) j))).trans (hCc (Classical.arbitrary I))
    have hm0 (i j : I) : 0 ≤ m i j := by
      have h := hm_triangle i j i
      rw [hm_self,hm_symm j i] at h
      linarith
    have hp := DobrushinSeries.powers_nonneg C hC
    have hw := DobrushinSeries.weighted_powers m hm_self hm_triangle C hC c hc0 hCc
    have hb (n : ℕ) (i j : I) : (C^n) i j ≤ c^n := by
      calc
        (C^n) i j ≤ Real.exp (m i j) * (C^n) i j := by
          have he : 1 ≤ Real.exp (m i j) := Real.one_le_exp_iff.mpr (hm0 i j)
          nlinarith [hp n i j]
        _ ≤ ∑ k, Real.exp (m i k) * (C^n) i k :=
          Finset.single_le_sum (fun k _ => mul_nonneg (Real.exp_pos _).le (hp n i k))
            (Finset.mem_univ j)
        _ ≤ c^n := hw n i
    have hs (i j : I) : Summable (fun n : ℕ => (C^n) i j) :=
      Summable.of_nonneg_of_le (fun n => hp n i j) (fun n => hb n i j)
        (hasSum_geometric_of_lt_one hc0 hc).summable
    let D : Matrix I I ℝ := fun i j => ∑' n : ℕ, (C^n) i j
    have hD : HasSum (fun n : ℕ => C^n) D :=
      Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => (hs i j).hasSum
    have hD0 (i j : I) : 0 ≤ D i j := tsum_nonneg (fun n => hp n i j)
    have hrow (i : I) : ∑ j, Real.exp (m i j) * D i j ≤ 1 / (1-c) := by
      have hh : HasSum (fun n : ℕ => ∑ j, Real.exp (m i j) * (C^n) i j)
          (∑ j, Real.exp (m i j) * D i j) :=
        hasSum_sum (fun j _ => (hs i j).hasSum.mul_left (Real.exp (m i j)))
      simpa only [one_div] using hasSum_le (fun n => hw n i) hh
        (hasSum_geometric_of_lt_one hc0 hc)
    refine ⟨D,hD,hrow,?_⟩
    intro i J hJ
    have hweighted : Real.exp (J.inf' hJ (m i)) * (∑ j ∈ J, D i j) ≤ 1/(1-c) := by
      calc
        _ = ∑ j ∈ J, Real.exp (J.inf' hJ (m i)) * D i j := Finset.mul_sum ..
        _ ≤ ∑ j ∈ J, Real.exp (m i j) * D i j := by
          exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (Finset.inf'_le _ hj)) (hD0 i j)
        _ ≤ ∑ j, Real.exp (m i j) * D i j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            (fun j _ _ => mul_nonneg (Real.exp_pos _).le (hD0 i j))
        _ ≤ _ := hrow i
    have he := mul_le_mul_of_nonneg_left hweighted (Real.exp_pos (-(J.inf' hJ (m i)))).le
    simpa only [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul,
      mul_one_div] using he

#print axioms solution
