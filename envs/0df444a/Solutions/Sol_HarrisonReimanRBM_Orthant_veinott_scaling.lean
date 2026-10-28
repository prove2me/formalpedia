-- Prove2me | solution 1 for HarrisonReimanRBM.Orthant.veinott_scaling
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:51:33.706002+00:00
-- url     : https://prove2.me/submissions/70526234-55c9-41b9-8a27-0b740a9f1dd3

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

open Filter Topology Matrix

namespace Aux_HR_veinott

lemma pow_nonneg' {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    ∀ k : ℕ, ∀ i j, 0 ≤ (Q ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hQ l j))

end Aux_HR_veinott

open HarrisonReimanRBM.Orthant in
theorem solution {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) :
    ∃ d : Fin K → ℝ, (∀ i, 0 < d i) ∧ maxRowSum (rescaleMatrix d Q) < 1 := by
  set v : Fin K → ℝ := fun _ => 1 with hv
  have hnn := Aux_HR_veinott.pow_nonneg' Q hQ.nonneg
  -- eventually all row sums of Q^N are < 1
  have hrow : ∀ i, Tendsto (fun m : ℕ => (Q ^ m *ᵥ v) i) atTop (𝓝 0) := by
    intro i
    have : (fun m : ℕ => (Q ^ m *ᵥ v) i) = fun m => ∑ j, (Q ^ m) i j := by
      funext m; simp [Matrix.mulVec, dotProduct, hv]
    rw [this]
    have h0 : (0 : ℝ) = ∑ j : Fin K, (0 : Matrix (Fin K) (Fin K) ℝ) i j := by simp
    rw [h0]
    apply tendsto_finset_sum
    intro j _
    exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp
      hQ.pow_tendsto_zero
  have hev : ∀ᶠ m in atTop, 1 ≤ m ∧ ∀ i, (Q ^ m *ᵥ v) i < 1 := by
    refine (eventually_ge_atTop 1).and ?_
    rw [eventually_all]
    intro i
    exact (hrow i).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN1, hNlt⟩ := hev.exists
  set d : Fin K → ℝ := ∑ k ∈ Finset.range N, Q ^ k *ᵥ v with hd
  have hcomp : ∀ k i, 0 ≤ (Q ^ k *ᵥ v) i := by
    intro k i
    simp only [Matrix.mulVec, dotProduct, hv, mul_one]
    exact Finset.sum_nonneg (fun j _ => hnn k i j)
  have hd1 : ∀ i, 1 ≤ d i := by
    intro i
    rw [hd, Finset.sum_apply]
    have h0 : (Q ^ 0 *ᵥ v) i = 1 := by simp [hv]
    calc (1 : ℝ) = (Q ^ 0 *ᵥ v) i := h0.symm
      _ ≤ ∑ k ∈ Finset.range N, (Q ^ k *ᵥ v) i :=
        Finset.single_le_sum (fun k _ => hcomp k i) (Finset.mem_range.mpr (by omega))
  have hdpos : ∀ i, 0 < d i := fun i => lt_of_lt_of_le one_pos (hd1 i)
  -- Q d = d + Q^N v - v
  have hQd : Q *ᵥ d = d + Q ^ N *ᵥ v - v := by
    have h1 : Q *ᵥ d = ∑ k ∈ Finset.range N, Q ^ (k + 1) *ᵥ v := by
      rw [hd, Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.mulVec_mulVec, pow_succ']
    have h2 : ∑ k ∈ Finset.range (N + 1), Q ^ k *ᵥ v =
        ∑ k ∈ Finset.range N, Q ^ (k + 1) *ᵥ v + Q ^ 0 *ᵥ v := Finset.sum_range_succ' _ _
    have h3 : ∑ k ∈ Finset.range (N + 1), Q ^ k *ᵥ v = d + Q ^ N *ᵥ v := by
      rw [Finset.sum_range_succ]
    rw [h1]
    have h4 : Q ^ 0 *ᵥ v = v := by simp
    rw [h4] at h2
    rw [← h3, h2]
    abel
  refine ⟨d, hdpos, ?_⟩
  -- row sums
  have hrs : ∀ i, ∑ j, rescaleMatrix d Q i j < 1 := by
    intro i
    have e : ∑ j, rescaleMatrix d Q i j = (d i)⁻¹ * (Q *ᵥ d) i := by
      unfold rescaleMatrix
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mulVec, dotProduct,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e, hQd]
    simp only [Pi.add_apply, Pi.sub_apply]
    have hlt := hNlt i
    have hvi : v i = 1 := rfl
    rw [hvi, inv_mul_lt_iff₀ (hdpos i)]
    linarith
  unfold maxRowSum
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ∑ j, rescaleMatrix d Q i j)
  rw [← hi]
  exact hrs i
