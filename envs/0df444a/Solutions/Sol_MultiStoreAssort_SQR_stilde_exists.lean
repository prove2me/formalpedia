-- Prove2me | solution 1 for MultiStoreAssort.SQR.stilde_exists
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:58:30.20127+00:00
-- url     : https://prove2.me/submissions/c4440204-9966-491f-be0d-77cf6f6c303e

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

set_option autoImplicit false

theorem solution {n : ℕ} (r v : Fin n → ℝ) (hn : 0 < n) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) :
    ∃ St : Finset (Fin n), MultiStoreAssort.SMR.IsStilde r v St := by
  classical
  obtain ⟨T, -, hT⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
    (fun S => MultiStoreAssort.SMR.single r v S) ⟨∅, Finset.mem_univ _⟩
  have hTmax : ∀ S : Finset (Fin n), MultiStoreAssort.SMR.single r v S ≤ MultiStoreAssort.SMR.single r v T :=
    fun S => hT S (Finset.mem_univ _)
  have hsingle : ∀ S : Finset (Fin n), MultiStoreAssort.SMR.single r v S =
      (∑ j ∈ S, r j * v j) / (∑ j ∈ S, v j + 1) := fun S => rfl
  have hpos : ∀ S : Finset (Fin n), 0 < ∑ j ∈ S, v j + 1 := fun S =>
    by have := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).le); linarith
  set R := MultiStoreAssort.SMR.single r v T with hR
  have key : R * (∑ j ∈ T, v j + 1) = ∑ j ∈ T, r j * v j := by
    rw [hR, hsingle, div_mul_cancel₀ _ (hpos T).ne']
  have h1 : ∑ j ∈ T, v j * (r j - R) = R := by
    have : ∑ j ∈ T, v j * (r j - R) = ∑ j ∈ T, r j * v j - R * ∑ j ∈ T, v j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; linarith
  set S0 : Finset (Fin n) := Finset.univ.filter (fun j => R < r j) with hS0
  have h2 : ∑ j ∈ T, v j * (r j - R) ≤ ∑ j ∈ S0, v j * (r j - R) := by
    calc ∑ j ∈ T, v j * (r j - R) ≤ ∑ j ∈ T.filter (fun j => R < r j), v j * (r j - R) := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum
          intro j _
          by_cases h : R < r j
          · rw [if_pos h]
          · rw [if_neg h]
            exact mul_nonpos_of_nonneg_of_nonpos (hv j).le (by linarith [not_lt.1 h])
      _ ≤ ∑ j ∈ S0, v j * (r j - R) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [Finset.mem_filter] at hj
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.2⟩
          · intro j hj _
            rw [hS0, Finset.mem_filter] at hj
            exact mul_nonneg (hv j).le (by linarith [hj.2])
  have hS0ge : R ≤ MultiStoreAssort.SMR.single r v S0 := by
    rw [hsingle, le_div_iff₀ (hpos S0)]
    have h3 : ∑ j ∈ S0, v j * (r j - R) = ∑ j ∈ S0, r j * v j - R * ∑ j ∈ S0, v j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    nlinarith
  have hS0opt : MultiStoreAssort.SMR.IsOptSingle r v S0 := by
    intro U
    exact (hTmax U).trans hS0ge
  -- R < r 0
  have hr0 : R < r ⟨0, hn⟩ := by
    rw [hR, hsingle, div_lt_iff₀ (hpos T)]
    have h4 : ∑ j ∈ T, r j * v j ≤ ∑ j ∈ T, r ⟨0, hn⟩ * v j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (hr.antitone (Fin.mk_le_mk.2 (Nat.zero_le _))) (hv j).le)
    rw [← Finset.mul_sum] at h4
    nlinarith [hrpos ⟨0, hn⟩]
  have hne : S0.Nonempty := ⟨⟨0, hn⟩, by rw [hS0, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hr0⟩⟩
  set m := S0.max' hne with hm
  have hmS0 : m ∈ S0 := S0.max'_mem hne
  have hdown : ∀ k, k ≤ m → k ∈ S0 := by
    intro k hk
    have hm' : R < r m := (Finset.mem_filter.1 hmS0).2
    have : r m ≤ r k := hr.antitone hk
    rw [hS0, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by linarith⟩
  have hS0eq : S0 = MultiStoreAssort.SMR.prefixSet n (m.val + 1) := by
    ext k
    simp only [MultiStoreAssort.SMR.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have := S0.le_max' k hk
      have := Fin.le_def.1 this
      omega
    · intro hk
      exact hdown k (Fin.le_def.2 (by omega))
  have hS0rev : MultiStoreAssort.SMR.IsRevenueOrdered S0 :=
    ⟨m.val + 1, by omega, by have := m.isLt; omega, hS0eq⟩
  obtain ⟨St, hSt, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun S : Finset (Fin n) =>
      MultiStoreAssort.SMR.IsRevenueOrdered S ∧ MultiStoreAssort.SMR.IsOptSingle r v S))
    (fun S => S.card) ⟨S0, by simp [hS0rev, hS0opt]⟩
  rw [Finset.mem_filter] at hSt
  exact ⟨St, hSt.2.1, hSt.2.2, fun T' hT1 hT2 => hmin T' (by simp [hT1, hT2])⟩
