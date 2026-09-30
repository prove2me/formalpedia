-- Prove2me | solution 2 for Komlos.komlos_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T05:45:49.481047+00:00
-- url     : https://prove2.me/submissions/32b270d7-6f8b-4ba0-9049-fea94a9f68b5

import Mathlib
import Definitions.Def_Komlos_model

set_option autoImplicit false

open scoped BigOperators

namespace KomlosProof

lemma finite_matrix_bound {K : ℝ} (hK : Komlos.KomlosBound K)
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (hA : ∀ i, ∑ j, (A i j) ^ 2 ≤ 1) :
    ∃ eps : I → ℝ, (∀ i, eps i = 1 ∨ eps i = -1) ∧
      ∀ j, |∑ i, eps i * A i j| ≤ K := by
  classical
  let ei := Fintype.equivFin I
  let ej := Fintype.equivFin J
  let v : Fin (Fintype.card I) → EuclideanSpace ℝ (Fin (Fintype.card J)) :=
    fun i => WithLp.toLp 2 (fun j => A (ei.symm i) (ej.symm j))
  have hv : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have hsq : ‖v i‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ j, (A (ei.symm i) (ej.symm j)) ^ 2) ≤ 1
      rw [ej.symm.sum_comp (fun j : J => (A (ei.symm i) j) ^ 2)]
      exact hA (ei.symm i)
    nlinarith [norm_nonneg (v i)]
  rcases hK _ _ v hv with ⟨eps, heps, hb⟩
  refine ⟨fun i => eps (ei i), fun i => heps (ei i), ?_⟩
  intro j
  have heq : (∑ i, eps (ei i) * A i j) =
      ∑ a, eps a * v a (ej j) := by
    simpa [v] using ei.sum_comp (fun a => eps a * v a (ej j))
  rw [heq]
  exact hb (ej j)

lemma bound_nonneg {K : ℝ} (hK : Komlos.KomlosBound K) : 0 ≤ K := by
  rcases hK 0 1 (fun _ => 0) (by simp) with ⟨eps, _, hb⟩
  simpa using hb 0

-- Kunisky's normalized block construction, Eq. (17), acts on arbitrary
-- rectangular matrices; finite-index transport keeps both empty cases valid.
lemma transformed_bound {K : ℝ} (hK : Komlos.KomlosBound K) :
    Komlos.KomlosBound (Real.sqrt 2 * K - 1) := by
  classical
  intro n m v hv
  let c : ℝ := Real.sqrt 2 / 2
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc : 2 * c ^ 2 = 1 := by dsimp [c]; nlinarith
  have hcinv : Real.sqrt 2 * c = 1 := by dsimp [c]; nlinarith
  let B : (Fin n ⊕ Fin m) → (Fin m ⊕ Fin m) → ℝ := fun i j =>
    match i, j with
    | Sum.inl a, Sum.inl b => c * v a b
    | Sum.inl a, Sum.inr b => c * v a b
    | Sum.inr a, Sum.inl b => if b = a then c else 0
    | Sum.inr a, Sum.inr b => if b = a then -c else 0
  have hB : ∀ i, ∑ j, (B i j) ^ 2 ≤ 1 := by
    intro i
    rcases i with i | i
    · have hsq : ∑ j, (v i j) ^ 2 ≤ 1 := by
        rw [← EuclideanSpace.real_norm_sq_eq]
        nlinarith [hv i, norm_nonneg (v i)]
      simp only [B, Fintype.sum_sum_type, mul_pow, ← Finset.mul_sum]
      nlinarith
    · simp [B, Fintype.sum_sum_type]
      nlinarith
  rcases finite_matrix_bound hK B hB with ⟨eps, heps, hb⟩
  refine ⟨fun i => eps (Sum.inl i), fun i => heps (Sum.inl i), ?_⟩
  intro j
  let a : ℝ := ∑ i, eps (Sum.inl i) * v i j
  let b : ℝ := eps (Sum.inr j)
  have hplus : |c * (a + b)| ≤ K := by
    simpa [B, a, b, Fintype.sum_sum_type, mul_add, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc] using hb (Sum.inl j)
  have hminus : |c * (a - b)| ≤ K := by
    convert hb (Sum.inr j) using 1
    congr 1
    simp [B, a, b, Fintype.sum_sum_type, mul_add, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
  have hp : |a + b| ≤ Real.sqrt 2 * K := by
    have h := mul_le_mul_of_nonneg_left hplus hrootpos.le
    simpa [abs_mul, abs_of_pos hcpos, ← mul_assoc, hcinv] using h
  have hm : |a - b| ≤ Real.sqrt 2 * K := by
    have h := mul_le_mul_of_nonneg_left hminus hrootpos.le
    simpa [abs_mul, abs_of_pos hcpos, ← mul_assoc, hcinv] using h
  change |a| ≤ Real.sqrt 2 * K - 1
  rcases heps (Sum.inr j) with hsign | hsign
  · have hbval : b = 1 := hsign
    rw [hbval] at hp hm
    rcases abs_le.mp hp with ⟨hp1, hp2⟩
    rcases abs_le.mp hm with ⟨hm1, hm2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hbval : b = -1 := hsign
    rw [hbval] at hp hm
    rcases abs_le.mp hp with ⟨hp1, hp2⟩
    rcases abs_le.mp hm with ⟨hm1, hm2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end KomlosProof

theorem solution (K : ℝ) (hK : Komlos.KomlosBound K) :
    1 + Real.sqrt 2 ≤ K := by
  let S : Set ℝ := {t | Komlos.KomlosBound t}
  have hne : S.Nonempty := ⟨K, hK⟩
  have hbelow : BddBelow S := ⟨0, fun t ht => KomlosProof.bound_nonneg ht⟩
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootone : 1 < Real.sqrt 2 := by nlinarith
  have hnew : (sInf S + 1) / Real.sqrt 2 ≤ sInf S := by
    apply le_csInf hne
    intro t ht
    have htrans : Real.sqrt 2 * t - 1 ∈ S := KomlosProof.transformed_bound ht
    have hi := csInf_le hbelow htrans
    apply (div_le_iff₀ hrootpos).mpr
    nlinarith
  have hineq := (div_le_iff₀ hrootpos).mp hnew
  have hfixed : 1 + Real.sqrt 2 ≤ sInf S := by
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hrootone)).mp
    nlinarith
  exact hfixed.trans (csInf_le hbelow hK)

#print axioms solution
