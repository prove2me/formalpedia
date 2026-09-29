-- Prove2me | solution 1 for LassoDantzig.Dantzig.eq_B28
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:18:11.57932+00:00
-- url     : https://prove2.me/submissions/8fbfd525-1304-4564-97a4-ef9f46efed2d

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open LassoDantzig.Dantzig

private theorem b28 {M : ℕ} (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ)
    (hsub : J1 ⊆ J0ᶜ) (hcard : J1.card = m)
    (htop : ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|)
    (hcone : (∑ j ∈ J0ᶜ, |δ j|) ≤ c0 * ∑ j ∈ J0, |δ j|) :
    (Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2) ^ 2
        ≤ (1 / (m : ℝ)) * (∑ j ∈ J0ᶜ, |δ j|) ^ 2) ∧
    (Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2) ≤ c0 * (∑ j ∈ J0, |δ j|) / Real.sqrt m) ∧
    (c0 * (∑ j ∈ J0, |δ j|) / Real.sqrt m
        ≤ c0 * Real.sqrt (∑ j ∈ J0, δ j ^ 2) * Real.sqrt ((s : ℝ) / m)) ∧
    (c0 * Real.sqrt (∑ j ∈ J0, δ j ^ 2) * Real.sqrt ((s : ℝ) / m)
        ≤ c0 * Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2) * Real.sqrt ((s : ℝ) / m)) ∧
    (Real.sqrt (∑ j, δ j ^ 2)
        ≤ (1 + c0 * Real.sqrt ((s : ℝ) / m)) * Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hsum2nn : ∀ S : Finset (Fin M), (0 : ℝ) ≤ ∑ j ∈ S, δ j ^ 2 :=
    fun S => Finset.sum_nonneg fun j _ => sq_nonneg _
  have habsnn : ∀ S : Finset (Fin M), (0 : ℝ) ≤ ∑ j ∈ S, |δ j| :=
    fun S => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hcompl : (J0 ∪ J1)ᶜ = J0ᶜ \ J1 := by
    ext k
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    tauto
  -- the coordinates outside `J0 ∪ J1` are small
  have hkey : ∀ k ∈ (J0 ∪ J1)ᶜ, |δ k| ≤ (1 / (m : ℝ)) * ∑ j ∈ J0ᶜ, |δ j| := by
    intro k hk
    rw [hcompl] at hk
    have h1 : (m : ℝ) * |δ k| ≤ ∑ j ∈ J1, |δ j| := by
      calc (m : ℝ) * |δ k| = ∑ _j ∈ J1, |δ k| := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ j ∈ J1, |δ j| := Finset.sum_le_sum fun j hj => htop j hj k hk
    have h2 : ∑ j ∈ J1, |δ j| ≤ ∑ j ∈ J0ᶜ, |δ j| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => abs_nonneg _
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hmR]
    linarith
  -- part 1
  have hp1 : ∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2 ≤ (1 / (m : ℝ)) * (∑ j ∈ J0ᶜ, |δ j|) ^ 2 := by
    have hcoef : (0 : ℝ) ≤ (1 / (m : ℝ)) * ∑ k ∈ J0ᶜ, |δ k| :=
      mul_nonneg (by positivity) (habsnn _)
    calc ∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2 = ∑ j ∈ (J0 ∪ J1)ᶜ, |δ j| * |δ j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← sq_abs, sq]
      _ ≤ ∑ j ∈ (J0 ∪ J1)ᶜ, ((1 / (m : ℝ)) * ∑ k ∈ J0ᶜ, |δ k|) * |δ j| :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hkey j hj) (abs_nonneg _)
      _ = ((1 / (m : ℝ)) * ∑ k ∈ J0ᶜ, |δ k|) * ∑ j ∈ (J0 ∪ J1)ᶜ, |δ j| := by
          rw [← Finset.mul_sum]
      _ ≤ ((1 / (m : ℝ)) * ∑ k ∈ J0ᶜ, |δ k|) * ∑ j ∈ J0ᶜ, |δ j| := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          rw [hcompl]
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            fun _ _ _ => abs_nonneg _
      _ = (1 / (m : ℝ)) * (∑ j ∈ J0ᶜ, |δ j|) ^ 2 := by ring
  have hp1' : Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2) ^ 2
      ≤ (1 / (m : ℝ)) * (∑ j ∈ J0ᶜ, |δ j|) ^ 2 := by
    rw [Real.sq_sqrt (hsum2nn _)]
    exact hp1
  -- part 2
  have hQsq : ((∑ j ∈ J0ᶜ, |δ j|) / Real.sqrt m) ^ 2
      = (1 / (m : ℝ)) * (∑ j ∈ J0ᶜ, |δ j|) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hmR.le]
    ring
  have hB : Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2)
      ≤ (∑ j ∈ J0ᶜ, |δ j|) / Real.sqrt m := by
    have hQnn : (0 : ℝ) ≤ (∑ j ∈ J0ᶜ, |δ j|) / Real.sqrt m := by
      exact div_nonneg (habsnn _) hsm.le
    calc Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2)
        ≤ Real.sqrt (((∑ j ∈ J0ᶜ, |δ j|) / Real.sqrt m) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          rw [hQsq]
          exact hp1
      _ = (∑ j ∈ J0ᶜ, |δ j|) / Real.sqrt m := Real.sqrt_sq hQnn
  have hp2 : Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2)
      ≤ c0 * (∑ j ∈ J0, |δ j|) / Real.sqrt m := by
    refine le_trans hB ?_
    rw [div_le_div_iff₀ hsm hsm]
    exact mul_le_mul_of_nonneg_right hcone hsm.le
  -- Cauchy-Schwarz on J0
  have hcs : (∑ j ∈ J0, |δ j|) ≤ Real.sqrt s * Real.sqrt (∑ j ∈ J0, δ j ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt J0 (fun _ => (1 : ℝ)) (fun j => |δ j|)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (by exact_mod_cast hJ0)
  have hsqrtdiv : Real.sqrt ((s : ℝ) / m) = Real.sqrt s / Real.sqrt m :=
    Real.sqrt_div (by positivity) _
  have hp3 : c0 * (∑ j ∈ J0, |δ j|) / Real.sqrt m
      ≤ c0 * Real.sqrt (∑ j ∈ J0, δ j ^ 2) * Real.sqrt ((s : ℝ) / m) := by
    have hcan : Real.sqrt s / Real.sqrt m * Real.sqrt m = Real.sqrt s := by
      field_simp
    rw [hsqrtdiv, div_le_iff₀ hsm, mul_assoc, hcan]
    calc c0 * (∑ j ∈ J0, |δ j|)
        ≤ c0 * (Real.sqrt s * Real.sqrt (∑ j ∈ J0, δ j ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hc0.le
      _ = c0 * Real.sqrt (∑ j ∈ J0, δ j ^ 2) * Real.sqrt s := by ring
  -- part 4
  have hmono : Real.sqrt (∑ j ∈ J0, δ j ^ 2) ≤ Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ => sq_nonneg _
  have hp4 : c0 * Real.sqrt (∑ j ∈ J0, δ j ^ 2) * Real.sqrt ((s : ℝ) / m)
      ≤ c0 * Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2) * Real.sqrt ((s : ℝ) / m) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hmono hc0.le
  -- part 5
  have hsplit : ∑ j, δ j ^ 2
      = (∑ j ∈ J0 ∪ J1, δ j ^ 2) + ∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2 :=
    (Finset.sum_add_sum_compl (J0 ∪ J1) (fun j => δ j ^ 2)).symm
  have hp5 : Real.sqrt (∑ j, δ j ^ 2)
      ≤ (1 + c0 * Real.sqrt ((s : ℝ) / m)) * Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2) := by
    set A := Real.sqrt (∑ j ∈ J0 ∪ J1, δ j ^ 2) with hA
    set B := Real.sqrt (∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2) with hBdef
    have hAnn : 0 ≤ A := Real.sqrt_nonneg _
    have hBnn : 0 ≤ B := Real.sqrt_nonneg _
    have hBle : B ≤ c0 * A * Real.sqrt ((s : ℝ) / m) :=
      le_trans hp2 (le_trans hp3 hp4)
    have hAB : Real.sqrt (∑ j, δ j ^ 2) ≤ A + B := by
      have hX : ∑ j, δ j ^ 2 = A ^ 2 + B ^ 2 := by
        rw [hA, hBdef, Real.sq_sqrt (hsum2nn _), Real.sq_sqrt (hsum2nn _)]
        exact hsplit
      rw [hX]
      have h2 : A ^ 2 + B ^ 2 ≤ (A + B) ^ 2 := by nlinarith [mul_nonneg hAnn hBnn]
      calc Real.sqrt (A ^ 2 + B ^ 2) ≤ Real.sqrt ((A + B) ^ 2) := Real.sqrt_le_sqrt h2
        _ = A + B := Real.sqrt_sq (by linarith)
    calc Real.sqrt (∑ j, δ j ^ 2) ≤ A + B := hAB
      _ ≤ A + c0 * A * Real.sqrt ((s : ℝ) / m) := by linarith
      _ = (1 + c0 * Real.sqrt ((s : ℝ) / m)) * A := by ring
  exact ⟨hp1', hp2, hp3, hp4, hp5⟩

theorem solution {M : ℕ} (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ)
    (hJ1 : IsTopBlock δ J0 J1 m) (hcone : ConeCond c0 J0 δ) :
    l2On δ (J0 ∪ J1)ᶜ ^ 2 ≤ (1 / (m : ℝ)) * l1On δ J0ᶜ ^ 2 ∧
    l2On δ (J0 ∪ J1)ᶜ ≤ c0 * l1On δ J0 / Real.sqrt m ∧
    c0 * l1On δ J0 / Real.sqrt m ≤ c0 * l2On δ J0 * Real.sqrt ((s : ℝ) / m) ∧
    c0 * l2On δ J0 * Real.sqrt ((s : ℝ) / m) ≤ c0 * l2On δ (J0 ∪ J1) * Real.sqrt ((s : ℝ) / m) ∧
    Real.sqrt (∑ j, δ j ^ 2) ≤ (1 + c0 * Real.sqrt ((s : ℝ) / m)) * l2On δ (J0 ∪ J1) := by
  obtain ⟨hsub, hcard, htop⟩ := hJ1
  have hc : (∑ j ∈ J0ᶜ, |δ j|) ≤ c0 * ∑ j ∈ J0, |δ j| := hcone
  simp only [l1On, l2On]
  exact b28 s m hm c0 hc0 J0 J1 hJ0 δ hsub hcard htop hc
