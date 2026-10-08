-- Prove2me | solution 1 for KellyReversibility.Allocation.optimal_capacity_allocation
-- status  : ACCEPTED   (prove)
-- author  : @techtao
-- created : 2026-10-05T03:43:39.200986+00:00
-- url     : https://prove2.me/submissions/aae6da1d-257c-4e08-b304-9b1e4e329966

import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation
set_option autoImplicit false

-- Exact target: https://prove2.me/theorems/3d43bc0f-26cb-437f-90c4-1299cdb046fb
-- Every helper is closed locally; no target theorem or open lemma is imported.


set_option autoImplicit false
open scoped BigOperators
open KellyReversibility.Allocation

namespace CapacityWork

private lemma scalar_minimum (a b s t : ℝ) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (heq : b * s ^ 2 = a) :
    a / s + b * s ≤ a / t + b * t := by
  have hdiv : a / s = b * s := (div_eq_iff (ne_of_gt hs)).2 (by nlinarith [heq])
  have h : 2 * b * s - b * t ≤ a / t := by
    apply (le_div_iff₀ ht).2
    nlinarith [mul_nonneg (le_of_lt hb) (sq_nonneg (t - s))]
  rw [hdiv]
  linarith

private lemma scalar_minimum_strict (a b s t : ℝ) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (heq : b * s ^ 2 = a) (hne : t ≠ s) :
    a / s + b * s < a / t + b * t := by
  have hdiv : a / s = b * s := (div_eq_iff (ne_of_gt hs)).2 (by nlinarith [heq])
  have h : 2 * b * s - b * t < a / t := by
    apply (lt_div_iff₀ ht).2
    have hp : 0 < b * (t - s) ^ 2 := mul_pos hb (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    nlinarith
  rw [hdiv]
  linarith

theorem lagrangian_minimizer {J : ℕ} (a f : Fin J → ℝ) (F y : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hy : 0 < y) :
    let φstar : Fin J → ℝ := fun j => a j + Real.sqrt (a j / (y * f j))
    (∀ j, a j < φstar j) ∧
      ∀ φ : Fin J → ℝ, (∀ j, a j < φ j) → φ ≠ φstar →
        lagrangian a f F y φstar < lagrangian a f F y φ := by
  dsimp only
  let s : Fin J → ℝ := fun j => Real.sqrt (a j / (y * f j))
  have hs (j : Fin J) : 0 < s j := Real.sqrt_pos.2 (div_pos (ha j) (mul_pos hy (hf j)))
  have heq (j : Fin J) : (y * f j) * (s j) ^ 2 = a j := by
    dsimp [s]
    rw [Real.sq_sqrt (le_of_lt (div_pos (ha j) (mul_pos hy (hf j))))]
    field_simp [ne_of_gt hy, ne_of_gt (hf j)]
  constructor
  · intro j
    exact lt_add_of_pos_right _ (hs j)
  · intro φ hφ hne
    have hex : ∃ j, φ j ≠ a j + s j := by
      by_contra! h
      exact hne (funext h)
    obtain ⟨j, hj⟩ := hex
    have hle (i : Fin J) :
        a i / s i + y * f i * (a i + s i) ≤ a i / (φ i - a i) + y * f i * φ i := by
      have h := scalar_minimum (a i) (y * f i) (s i) (φ i - a i)
        (mul_pos hy (hf i)) (hs i) (sub_pos.mpr (hφ i)) (heq i)
      nlinarith
    have hlt :
        a j / s j + y * f j * (a j + s j) < a j / (φ j - a j) + y * f j * φ j := by
      have h := scalar_minimum_strict (a j) (y * f j) (s j) (φ j - a j)
        (mul_pos hy (hf j)) (hs j) (sub_pos.mpr (hφ j)) (heq j)
        (by intro h; apply hj; linarith)
      nlinarith
    have hsum :
        (∑ i, (a i / s i + y * f i * (a i + s i))) <
        ∑ i, (a i / (φ i - a i) + y * f i * φ i) := by
      exact Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hlt⟩
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
    simp only [lagrangian, meanNumberInNetwork, add_sub_cancel_left]
    dsimp only [s] at hsum
    linarith

end CapacityWork


open KellyReversibility.Allocation

namespace CapacityWork

theorem multiplier_choice {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    let y : ℝ := ((∑ k, Real.sqrt (a k * f k)) / (F - ∑ k, a k * f k)) ^ 2
    0 < y ∧ 1 / Real.sqrt y = (F - ∑ k, a k * f k) / ∑ k, Real.sqrt (a k * f k) ∧
      (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F := by
  classical
  let A : ℝ := ∑ k : Fin J, a k * f k
  let S : ℝ := ∑ k : Fin J, Real.sqrt (a k * f k)
  let T : ℝ := F - A
  let y : ℝ := (S / T) ^ 2
  change 0 < y ∧ 1 / Real.sqrt y = T / S ∧
    (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
    ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F

  have hprod : ∀ j : Fin J, 0 < a j * f j := fun j => mul_pos (ha j) (hf j)
  have hS : 0 < S := by
    dsimp [S]
    apply Finset.sum_pos
    · intro j hj
      exact Real.sqrt_pos.2 (hprod j)
    · apply Finset.card_pos.mp
      simpa using hJ
  have hA_lt_F : A < F := by simpa [A] using hF
  have hT : 0 < T := by
    dsimp [T]
    exact sub_pos.mpr hA_lt_F
  have hS_ne : S ≠ 0 := ne_of_gt hS
  have hT_ne : T ≠ 0 := ne_of_gt hT

  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hroot : Real.sqrt y = S / T := by
    dsimp [y]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hS hT)]
  have hrecip : 1 / Real.sqrt y = T / S := by
    rw [hroot]
    field_simp [hS_ne, hT_ne]

  have hpoint : ∀ j : Fin J,
      a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j := by
    intro j
    have haf : 0 < a j * f j := hprod j
    have hrad : a j / (y * f j) =
        ((T / S) * (Real.sqrt (a j * f j) / f j)) ^ 2 := by
      dsimp [y]
      field_simp [hS_ne, hT_ne, ne_of_gt (hf j)]
      rw [Real.sq_sqrt (le_of_lt haf)]
    have hfactor_pos : 0 < (T / S) * (Real.sqrt (a j * f j) / f j) :=
      mul_pos (div_pos hT hS)
        (div_pos (Real.sqrt_pos.2 haf) (hf j))
    change a j + Real.sqrt (a j / (y * f j)) =
      a j + (Real.sqrt (a j * f j) / S) * (T / f j)
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hfactor_pos]
    congr 1
    field_simp [hS_ne, ne_of_gt (hf j)]

  have hbudget_term : ∀ j : Fin J,
      f j * (a j + Real.sqrt (a j / (y * f j))) =
        f j * a j + (T / S) * Real.sqrt (a j * f j) := by
    intro j
    rw [hpoint j]
    change f j * (a j + (Real.sqrt (a j * f j) / S) * (T / f j)) =
      f j * a j + (T / S) * Real.sqrt (a j * f j)
    field_simp [hS_ne, ne_of_gt (hf j)]

  have hsum_fa : (∑ j : Fin J, f j * a j) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro j hj
    ring

  have hbudget : ∑ j : Fin J,
      f j * (a j + Real.sqrt (a j / (y * f j))) = F := by
    calc
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) =
          ∑ j, (f j * a j + (T / S) * Real.sqrt (a j * f j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hbudget_term j
      _ = (∑ j, f j * a j) + (T / S) * S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = F := by
        rw [hsum_fa]
        dsimp [T]
        rw [div_mul_cancel₀ _ hS_ne]
        ring

  exact ⟨hy, hrecip, hpoint, hbudget⟩

end CapacityWork


set_option autoImplicit false
open KellyReversibility.Allocation
open scoped BigOperators
namespace CapacityWork

theorem optimal_capacity_allocation {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    optimalAllocation a f F ∈ FeasibleCapacities a f F ∧
      IsMinOn (meanNumberInNetwork a) (FeasibleCapacities a f F) (optimalAllocation a f F) ∧
      ∀ φ ∈ FeasibleCapacities a f F, φ ≠ optimalAllocation a f F →
        meanNumberInNetwork a (optimalAllocation a f F) < meanNumberInNetwork a φ := by
  let y : ℝ := ((∑ k, Real.sqrt (a k * f k)) / (F - ∑ k, a k * f k)) ^ 2
  let φstar : Fin J → ℝ := fun j => a j + Real.sqrt (a j / (y * f j))
  have hm := multiplier_choice hJ a f F ha hf hF
  change 0 < y ∧ 1 / Real.sqrt y = (F - ∑ k, a k * f k) /
      ∑ k, Real.sqrt (a k * f k) ∧
      (∀ j, φstar j = optimalAllocation a f F j) ∧
      ∑ j, f j * φstar j = F at hm
  rcases hm with ⟨hy, _, hcoord, hcost⟩
  have hlag := lagrangian_minimizer a f F y ha hf hy
  change (∀ j, a j < φstar j) ∧
      ∀ φ : Fin J → ℝ, (∀ j, a j < φ j) → φ ≠ φstar →
        lagrangian a f F y φstar < lagrangian a f F y φ at hlag
  have hident : φstar = optimalAllocation a f F := by
    funext j
    exact hcoord j
  have hstable : ∀ j, a j < optimalAllocation a f F j := by
    intro j
    rw [← hident]
    exact hlag.1 j
  have hcoststar : ∑ j, f j * optimalAllocation a f F j = F := by
    rw [← hident]
    exact hcost
  have hfeas : optimalAllocation a f F ∈ FeasibleCapacities a f F :=
    ⟨hstable, hcoststar⟩
  have hstrict : ∀ φ ∈ FeasibleCapacities a f F, φ ≠ optimalAllocation a f F →
      meanNumberInNetwork a (optimalAllocation a f F) < meanNumberInNetwork a φ := by
    intro φ hφ hneq
    obtain ⟨hφstable, hφcost⟩ := hφ
    have hneq' : φ ≠ φstar := by
      rwa [hident]
    have h := hlag.2 φ hφstable hneq'
    rw [hident] at h
    change meanNumberInNetwork a (optimalAllocation a f F) +
        y * ((∑ j, f j * optimalAllocation a f F j) - F) <
      meanNumberInNetwork a φ + y * ((∑ j, f j * φ j) - F) at h
    rw [hcoststar, hφcost] at h
    simpa using h
  refine ⟨hfeas, ?_, hstrict⟩
  change ∀ φ, φ ∈ FeasibleCapacities a f F →
    meanNumberInNetwork a (optimalAllocation a f F) ≤ meanNumberInNetwork a φ
  intro φ hφ
  by_cases h : φ = optimalAllocation a f F
  · rw [h]
  · exact le_of_lt (hstrict φ hφ h)

end CapacityWork

theorem solution {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    optimalAllocation a f F ∈ FeasibleCapacities a f F ∧
      IsMinOn (meanNumberInNetwork a) (FeasibleCapacities a f F) (optimalAllocation a f F) ∧
      ∀ φ ∈ FeasibleCapacities a f F, φ ≠ optimalAllocation a f F →
        meanNumberInNetwork a (optimalAllocation a f F) < meanNumberInNetwork a φ := by
  exact CapacityWork.optimal_capacity_allocation hJ a f F ha hf hF

#print axioms solution
