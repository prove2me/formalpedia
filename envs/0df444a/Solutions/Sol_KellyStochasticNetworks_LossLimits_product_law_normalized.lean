-- Prove2me | solution 1 for KellyStochasticNetworks.LossLimits.product_law_normalized
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:56:36.962835+00:00
-- url     : https://prove2.me/submissions/902f5423-1150-4a80-b47d-0822dcfaf24e

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws

open MeasureTheory
open KellyStochasticNetworks

theorem g79w_summable {R : ℕ} (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) :
    Summable (fun n : Fin R → ℕ => lossWeight ν n) := by
  have hf : ∀ r, Summable (fun k : ℕ => ν r ^ k / (Nat.factorial k : ℝ)) :=
    fun r => Real.summable_pow_div_factorial (ν r)
  have hnn : ∀ r k, 0 ≤ ν r ^ k / (Nat.factorial k : ℝ) := fun r k => by
    have := hν r; positivity
  refine summable_of_sum_le (c := ∏ r, ∑' k, ν r ^ k / (Nat.factorial k : ℝ))
    (fun n => Finset.prod_nonneg fun r _ => hnn r (n r)) fun u => ?_
  set t : Fin R → Finset ℕ := fun r => u.image (fun n => n r)
  have hsub : u ⊆ Fintype.piFinset t := by
    intro n hn; rw [Fintype.mem_piFinset]; intro r; exact Finset.mem_image_of_mem _ hn
  calc ∑ n ∈ u, lossWeight ν n ≤ ∑ n ∈ Fintype.piFinset t, lossWeight ν n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          Finset.prod_nonneg fun r _ => hnn r (n r)
    _ = ∏ r, ∑ k ∈ t r, ν r ^ k / (Nat.factorial k : ℝ) := by
        rw [Finset.prod_univ_sum]; rfl
    _ ≤ ∏ r, ∑' k, ν r ^ k / (Nat.factorial k : ℝ) :=
        Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun k _ => hnn r k)
          fun r _ => (hf r).sum_le_tsum _ fun k _ => hnn r k

theorem g79w_pos {R : ℕ} (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r) (n : Fin R → ℕ) :
    0 < lossWeight ν n := Finset.prod_pos fun r _ => by have := hν r; positivity

theorem g79w_Tin {R : ℕ} (ν : Fin R → ℝ) (k : Fin R) (n : Fin R → ℕ) :
    lossWeight ν (Tin k n) * ((n k : ℝ) + 1) = lossWeight ν n * ν k := by
  unfold lossWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hrest : ∏ x ∈ Finset.univ.erase k, ν x ^ Tin k n x / ((Tin k n x).factorial : ℝ) =
      ∏ x ∈ Finset.univ.erase k, ν x ^ n x / ((n x).factorial : ℝ) :=
    Finset.prod_congr rfl fun x hx => by
      simp only [Tin, if_neg (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  simp only [Tin, if_true]
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have : ((n k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem g79w_rates {R : ℕ} (ν : Fin R → ℝ) (n m : Fin R → ℕ) :
    openMigrationRates (fun _ _ => (0:ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)) n m =
      (∑ j, if m = Tout j n then (n j : ℝ) else 0) + ∑ k, if m = Tin k n then ν k else 0 := by
  unfold openMigrationRates closedMigrationRates
  simp

theorem g79w_TinTout {R : ℕ} (k : Fin R) (n : Fin R → ℕ) : Tout k (Tin k n) = n := by
  funext i; simp only [Tout, Tin]; split_ifs with h <;> simp [h]

theorem g79w_ToutTin {R : ℕ} (k : Fin R) (n : Fin R → ℕ) (h : 0 < n k) : Tin k (Tout k n) = n := by
  funext i; simp only [Tout, Tin]; split_ifs with h1 <;> simp [h1]; omega

theorem g79w_Tin_ne_Tout {R : ℕ} (k j : Fin R) (n : Fin R → ℕ) : Tin k n ≠ Tout j n := by
  intro h; have := congrFun h k
  by_cases hkj : k = j
  · subst hkj; simp only [Tin, Tout, if_true] at this; omega
  · simp only [Tin, Tout, if_true, hkj, if_false] at this; omega

theorem g79w_Tin_inj {R : ℕ} (k k' : Fin R) (n : Fin R → ℕ) : Tin k n = Tin k' n ↔ k = k' := by
  constructor
  · intro h; by_contra hne; have := congrFun h k
    simp only [Tin, if_true, hne, if_false] at this; omega
  · rintro rfl; rfl

theorem g79w_Tin_ne_self {R : ℕ} (k : Fin R) (n m : Fin R → ℕ) (hle : ∀ i, n i ≤ m i) :
    n ≠ Tin k m := by
  intro h; have := congrFun h k; simp only [Tin, if_true] at this; have := hle k; omega

/-- the case m = Tin k n -/
theorem g79w_case {R : ℕ} (ν : Fin R → ℝ) (k : Fin R) (n : Fin R → ℕ) :
    lossWeight ν n * ((∑ j, if Tin k n = Tout j n then (n j : ℝ) else 0) +
        ∑ k', if Tin k n = Tin k' n then ν k' else 0) =
    lossWeight ν (Tin k n) * ((∑ j, if n = Tout j (Tin k n) then ((Tin k n) j : ℝ) else 0) +
        ∑ k', if n = Tin k' (Tin k n) then ν k' else 0) := by
  have e1 : (∑ j, if Tin k n = Tout j n then (n j : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [if_neg (g79w_Tin_ne_Tout k j n)]
  have e2 : (∑ k', if Tin k n = Tin k' n then ν k' else 0) = ν k := by
    simp_rw [g79w_Tin_inj]; simp
  have e3 : (∑ j, if n = Tout j (Tin k n) then ((Tin k n) j : ℝ) else 0) = (n k : ℝ) + 1 := by
    rw [Finset.sum_eq_single k]
    · rw [if_pos (g79w_TinTout k n).symm]; simp [Tin]
    · intro j _ hj
      rw [if_neg]; intro h; have := congrFun h k
      simp only [Tout, Tin, if_neg (Ne.symm hj), if_true] at this; omega
    · simp
  have e4 : (∑ k', if n = Tin k' (Tin k n) then ν k' else 0) = 0 :=
    Finset.sum_eq_zero fun k' _ => by
      rw [if_neg (g79w_Tin_ne_self k' n (Tin k n) fun i => by by_cases h : i = k <;> simp [Tin, h])]
  rw [e1, e2, e3, e4, zero_add, add_zero, g79w_Tin]

theorem g79w_db {R : ℕ} (ν : Fin R → ℝ) (n m : Fin R → ℕ) :
    lossWeight ν n * ((∑ j, if m = Tout j n then (n j : ℝ) else 0) + ∑ k, if m = Tin k n then ν k else 0) =
    lossWeight ν m * ((∑ j, if n = Tout j m then (m j : ℝ) else 0) + ∑ k, if n = Tin k m then ν k else 0) := by
  by_cases h1 : ∃ k, m = Tin k n
  · obtain ⟨k, rfl⟩ := h1; exact g79w_case ν k n
  by_cases h2 : ∃ k, n = Tin k m
  · obtain ⟨k, rfl⟩ := h2; exact (g79w_case ν k m).symm
  push Not at h1 h2
  have z : ∀ a b : Fin R → ℕ, (∀ k, a ≠ Tin k b) → (∀ k, b ≠ Tin k a) →
      (∑ j, if a = Tout j b then (b j : ℝ) else 0) + (∑ k, if a = Tin k b then ν k else 0) = 0 := by
    intro a b ha hb
    rw [Finset.sum_eq_zero fun k _ => if_neg (ha k), add_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · rcases Nat.eq_zero_or_pos (b j) with h0 | h0
      · simp [h0]
      · exact absurd (by rw [h, g79w_ToutTin j b h0]) (hb j)
    · rfl
  rw [z m n h1 h2, z n m h2 h1]; simp

open KellyStochasticNetworks.LossLimits in
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) :
    0 < partition A ν C ∧
    HasSum (fun n : KellyStochasticNetworks.lossStates A C =>
      KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ)) (partition A ν C) ∧
    KellyStochasticNetworks.DetailedBalance
      (fun n : KellyStochasticNetworks.lossStates A C =>
        KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ) / partition A ν C)
      (KellyStochasticNetworks.truncatedRates
        (KellyStochasticNetworks.openMigrationRates (fun _ _ => (0 : ℝ))
          (fun _ => 1) ν (fun _ m => (m : ℝ)))
        (KellyStochasticNetworks.lossStates A C)) ∧
    IsProbabilityMeasure (occupancyLaw A ν C) ∧
    (∀ n : KellyStochasticNetworks.lossStates A C,
      (occupancyLaw A ν C) {(n : Fin R → ℕ)} =
        ENNReal.ofReal (KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ) / partition A ν C)) ∧
    (occupancyLaw A ν C) (KellyStochasticNetworks.lossStates A C)ᶜ = 0 := by
  set S := lossStates A C with hS
  set Z := partition A ν C with hZdef
  have hsumm : Summable (fun n : S => lossWeight ν (n : Fin R → ℕ)) :=
    (g79w_summable ν hν).subtype S
  have hHas : HasSum (fun n : S => lossWeight ν (n : Fin R → ℕ)) Z := hsumm.hasSum
  have h0 : (0 : Fin R → ℕ) ∈ S := fun j => by simp
  have hZ : 0 < Z := hsumm.tsum_pos (fun n => (g79w_pos ν hν _).le) ⟨0, h0⟩ (g79w_pos ν hν _)
  have hnn : ∀ n : S, 0 ≤ lossWeight ν (n : Fin R → ℕ) / Z := fun n =>
    div_nonneg (g79w_pos ν hν _).le hZ.le
  refine ⟨hZ, hHas, ?_, ?_, ?_, ?_⟩
  · intro j k
    simp only [truncatedRates]
    rw [g79w_rates, g79w_rates, div_mul_eq_mul_div, div_mul_eq_mul_div, g79w_db ν j k]
  · constructor
    rw [occupancyLaw, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hsumm.div_const Z), tsum_div_const]
    change ENNReal.ofReal (Z / Z) = 1
    rw [div_self hZ.ne', ENNReal.ofReal_one]
  · intro n
    rw [occupancyLaw, Measure.sum_apply _ (measurableSet_singleton _)]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [tsum_eq_single n]
    · rw [Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one]
    · intro m hm
      rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem, mul_zero]
      simp only [Set.mem_singleton_iff]; exact fun h => hm (Subtype.ext h)
  · rw [occupancyLaw, Measure.sum_apply _ (Set.to_countable _).measurableSet]
    refine ENNReal.tsum_eq_zero.mpr fun m => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet, Set.indicator_of_notMem, mul_zero]
    simp only [Set.mem_compl_iff, not_not]; exact m.2
