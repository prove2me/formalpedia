-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.ineq36
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:07:35.323072+00:00
-- url     : https://prove2.me/submissions/8c7d6371-44e6-42fb-91c1-34a4aabf20bc

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15

open NestedLogitAssort.DeltaGrid in
theorem solution {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hγ0 : 0 ≤ I.γ i) (γbar : ℝ) (δ : ℝ) (hδ : 1 < δ) (x : ℝ) (hx : 0 ≤ x)
    (l : ℤ) (S Shat : Finset (Fin n)) (hS : Window I δ i l S) (hShat : IsApprox15 I δ i l Shat)
    (yi : ℝ) (hy : T I i Shat x ≤ yi) :
    δ ^ γbar * (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
          (∑ j ∈ S, I.r i j * I.v i j) - δ ^ (γbar + 1) * (δ ^ l) ^ (I.γ i) * x ≤
        δ ^ (γbar + 1) * yi ∧
      δ ^ γbar * (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
          (∑ j ∈ S, I.r i j * I.v i j) - δ ^ (γbar + I.γ i + 1) * (δ ^ (l - 1)) ^ (I.γ i) * x ≤
        δ ^ (γbar + 1) * yi := by
  have hδpos : (0:ℝ) < δ := by linarith
  have hδne : δ ≠ 0 := hδpos.ne'
  have hL0 : (0:ℝ) < δ ^ l := zpow_pos hδpos l
  have hL1 : δ ^ (l - 1) = δ ^ l / δ := by rw [zpow_sub_one₀ hδne, div_eq_mul_inv]
  obtain ⟨hW1, hW2⟩ := hShat.1
  have hVpos : 0 < V I i Shat := lt_of_lt_of_le (zpow_pos hδpos _) hW1
  have hsum : ∑ j ∈ S, I.r i j * I.v i j ≤ δ * ∑ j ∈ Shat, I.r i j * I.v i j := hShat.2 S hS
  have hSh0 : 0 ≤ ∑ j ∈ Shat, I.r i j * I.v i j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j))
  -- T expansion
  have hT : V I i Shat ^ (I.γ i - 1) * (∑ j ∈ Shat, I.r i j * I.v i j) -
      V I i Shat ^ (I.γ i) * x ≤ yi := by
    have e : T I i Shat x = V I i Shat ^ (I.γ i - 1) * (∑ j ∈ Shat, I.r i j * I.v i j) -
        V I i Shat ^ (I.γ i) * x := by
      unfold T R
      rw [Real.rpow_sub_one hVpos.ne']
      ring
    rw [← e]; exact hy
  -- key coefficient bound
  have hc0 : 0 ≤ (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hδpos.le _)
  have hck : (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) ≤
      V I i Shat ^ (I.γ i - 1) := by
    by_cases hg : 1 ≤ I.γ i
    · rw [max_eq_left (show (0:ℝ) ≤ I.γ i - 1 by linarith), Real.rpow_neg hδpos.le, ← div_eq_mul_inv,
        ← Real.div_rpow hL0.le hδpos.le, ← hL1]
      exact Real.rpow_le_rpow (zpow_pos hδpos _).le hW1 (by linarith)
    · rw [max_eq_right (show I.γ i - 1 ≤ (0:ℝ) by linarith), neg_zero, Real.rpow_zero, mul_one]
      exact Real.rpow_le_rpow_of_nonpos hVpos hW2 (by linarith)
  have hB : V I i Shat ^ (I.γ i) ≤ (δ ^ l) ^ (I.γ i) :=
    Real.rpow_le_rpow hVpos.le hW2 hγ0
  have h1 : (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) * (∑ j ∈ S, I.r i j * I.v i j) ≤
      δ * (V I i Shat ^ (I.γ i - 1) * (∑ j ∈ Shat, I.r i j * I.v i j)) := by
    calc (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) * (∑ j ∈ S, I.r i j * I.v i j)
        ≤ (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
            (δ * ∑ j ∈ Shat, I.r i j * I.v i j) := mul_le_mul_of_nonneg_left hsum hc0
      _ ≤ V I i Shat ^ (I.γ i - 1) * (δ * ∑ j ∈ Shat, I.r i j * I.v i j) :=
          mul_le_mul_of_nonneg_right hck (mul_nonneg hδpos.le hSh0)
      _ = δ * (V I i Shat ^ (I.γ i - 1) * (∑ j ∈ Shat, I.r i j * I.v i j)) := by ring
  have h2 : δ * (V I i Shat ^ (I.γ i) * x) ≤ δ * ((δ ^ l) ^ (I.γ i) * x) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hx) hδpos.le
  have h3 : δ * (V I i Shat ^ (I.γ i - 1) * (∑ j ∈ Shat, I.r i j * I.v i j) -
      V I i Shat ^ (I.γ i) * x) ≤ δ * yi := mul_le_mul_of_nonneg_left hT hδpos.le
  have h4 : (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) * (∑ j ∈ S, I.r i j * I.v i j) -
      δ * ((δ ^ l) ^ (I.γ i) * x) ≤ δ * yi := by
    linarith
  have hP : 0 ≤ δ ^ γbar := Real.rpow_nonneg hδpos.le _
  have h5 := mul_le_mul_of_nonneg_left h4 hP
  have hadd : δ ^ (γbar + 1) = δ ^ γbar * δ := Real.rpow_add_one hδne γbar
  have claim1 : δ ^ γbar * (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
          (∑ j ∈ S, I.r i j * I.v i j) - δ ^ (γbar + 1) * (δ ^ l) ^ (I.γ i) * x ≤
        δ ^ (γbar + 1) * yi := by
    rw [hadd]
    linarith
  refine ⟨claim1, ?_⟩
  have hdg : δ ^ (I.γ i) ≠ 0 := (Real.rpow_pos_of_pos hδpos _).ne'
  have e2 : δ ^ (γbar + I.γ i + 1) * (δ ^ (l - 1)) ^ (I.γ i) =
      δ ^ (γbar + 1) * (δ ^ l) ^ (I.γ i) := by
    rw [hL1, Real.div_rpow hL0.le hδpos.le, show γbar + I.γ i + 1 = (γbar + 1) + I.γ i by ring,
      Real.rpow_add hδpos]
    field_simp
  rw [e2]
  exact claim1
