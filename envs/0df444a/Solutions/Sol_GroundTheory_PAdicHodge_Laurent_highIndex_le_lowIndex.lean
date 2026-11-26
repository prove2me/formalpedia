-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.highIndex_le_lowIndex
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:49:10.505271+00:00
-- url     : https://prove2.me/submissions/b6d6031e-1752-45d4-8b77-177a0c925884

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}

private theorem bddAbove_gaussWeights (hρ : 0 < ρ) (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at hε
  set s1 : Set ℤ := {x | ¬ dist (f x) 0 < 1}
  have hFin : s1.Finite := Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) 1 one_pos)
  by_cases hN : hFin.toFinset.Nonempty
  · refine ⟨1 ⊔ hFin.toFinset.sup' hN f, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ hFin.toFinset
    · exact le_sup_of_le_right (Finset.le_sup' f hn)
    · have : n ∉ s1 := by
        rw [← hFin.mem_toFinset]
        exact hn
      have : dist (f n) 0 < 1 := by simpa [s1] using this
      exact le_sup_of_le_left (hlt_of_dist this).le
  · refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have : n ∉ s1 := by
      have : hFin.toFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
      rw [← hFin.mem_toFinset, this]
      exact Finset.notMem_empty n
    have : dist (f n) 0 < 1 := by simpa [s1] using this
    exact (hlt_of_dist this).le

private theorem gaussNorm_pos_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    0 < gaussNorm a ρ := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  obtain ⟨n, hn⟩ : ∃ n, a n ≠ 0 := by
    contrapose! ha
    exact funext ha
  have : 0 < f n := mul_pos (norm_pos_iff.mpr hn) (zpow_pos hρ n)
  exact this.trans_le (le_ciSup (bddAbove_gaussWeights hρ h) n)

private theorem domSet_nonempty_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    (domSet a ρ).Nonempty := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at hε
  have hbdd := bddAbove_gaussWeights (a := a) hρ h
  set M := ⨆ n, f n
  have hpos : 0 < M := by simpa [M, gaussNorm] using gaussNorm_pos_of (a := a) hρ h ha
  set s : Set ℤ := {n | ¬ dist (f n) 0 < M / 2}
  have hFin : s.Finite :=
    Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) (M / 2) (half_pos hpos))
  have hsN : s.Nonempty := by
    by_contra hsempty
    rw [Set.not_nonempty_iff_eq_empty] at hsempty
    have hall : ∀ n, f n < M / 2 := fun n => by
      have : n ∉ s := by rw [hsempty]; exact Set.notMem_empty n
      have : dist (f n) 0 < M / 2 := by simpa [s] using this
      exact hlt_of_dist this
    have : M ≤ M / 2 := ciSup_le fun n => (hall n).le
    exact (not_le.mpr (half_lt_self hpos)) this
  obtain ⟨n, hn, hnmax⟩ :=
    hFin.toFinset.exists_max_image f (hFin.toFinset_nonempty.mpr hsN)
  refine ⟨n, ?_⟩
  change f n = gaussNorm a ρ
  have hn_s : n ∈ s := hFin.mem_toFinset.mp hn
  have hnge : M / 2 ≤ f n := by
    have : ¬ dist (f n) 0 < M / 2 := by simpa [s] using hn_s
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at this
    exact not_lt.mp this
  refine le_antisymm (le_ciSup hbdd n) (ciSup_le fun m => ?_)
  by_cases hm : m ∈ s
  · exact hnmax m (hFin.mem_toFinset.mpr hm)
  · have : dist (f m) 0 < M / 2 := by simpa [s] using hm
    exact (hlt_of_dist this).le.trans hnge

private theorem domSet_finite_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    (domSet a ρ).Finite := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hpos := gaussNorm_pos_of (a := a) hρ h ha
  set M := ⨆ n, f n
  set s : Set ℤ := {n | ¬ dist (f n) 0 < M / 2}
  have hFin : s.Finite :=
    Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) (M / 2) (half_pos hpos))
  refine hFin.subset fun n hn => ?_
  change f n = gaussNorm a ρ at hn
  have hnge : M / 2 ≤ f n := by
    have : M ≤ f n := by simpa [M, gaussNorm] using le_of_eq hn.symm
    exact (half_le_self hpos.le).trans this
  have : ¬ dist (f n) 0 < M / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)]
    exact not_lt.mpr hnge
  simpa [s] using this

theorem solution {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ lowIndex a ρ' := by
  have hρ' : 0 < ρ' := hρ.trans hρρ'
  have hAne := domSet_nonempty_of (a := a) hρ h ha
  have hBne := domSet_nonempty_of (a := a) hρ' h' ha
  have hcmp : ∀ n ∈ domSet a ρ, ∀ m ∈ domSet a ρ', n ≤ m := by
    intro n hn m hm
    change ‖a n‖ * ρ ^ n = gaussNorm a ρ at hn
    change ‖a m‖ * ρ' ^ m = gaussNorm a ρ' at hm
    have hnpos : 0 < ‖a n‖ * ρ ^ n := by
      rw [hn]; exact gaussNorm_pos_of (a := a) hρ h ha
    have hmpos : 0 < ‖a m‖ * ρ' ^ m := by
      rw [hm]; exact gaussNorm_pos_of (a := a) hρ' h' ha
    have han : 0 < ‖a n‖ := (mul_pos_iff_of_pos_right (zpow_pos hρ n)).mp hnpos
    have ham : 0 < ‖a m‖ := (mul_pos_iff_of_pos_right (zpow_pos hρ' m)).mp hmpos
    have hle₁ : ‖a m‖ * ρ ^ m ≤ ‖a n‖ * ρ ^ n := by
      have := le_ciSup (bddAbove_gaussWeights (a := a) hρ h) m
      simpa [gaussNorm, hn] using this
    have hle₂ : ‖a n‖ * ρ' ^ n ≤ ‖a m‖ * ρ' ^ m := by
      have := le_ciSup (bddAbove_gaussWeights (a := a) hρ' h') n
      simpa [gaussNorm, hm] using this
    by_contra hnm
    have hnm : m < n := Int.not_le.mp hnm
    have h1 : ‖a m‖ / ‖a n‖ ≤ ρ ^ (n - m) := by
      have : ‖a m‖ ≤ ‖a n‖ * ρ ^ (n - m) := by
        rw [← mul_le_mul_iff_of_pos_right (zpow_pos hρ m), mul_assoc,
          ← zpow_add₀ hρ.ne', sub_add_cancel]
        exact hle₁
      exact (div_le_iff₀ han).mpr (by rwa [mul_comm] at this)
    have h2 : ρ' ^ (n - m) ≤ ‖a m‖ / ‖a n‖ := by
      have : ‖a n‖ * ρ' ^ (n - m) ≤ ‖a m‖ := by
        rw [← mul_le_mul_iff_of_pos_right (zpow_pos hρ' m), mul_assoc,
          ← zpow_add₀ hρ'.ne', sub_add_cancel]
        exact hle₂
      exact (le_div_iff₀ han).mpr (by rwa [mul_comm] at this)
    have hleρ : ρ' ^ (n - m) ≤ ρ ^ (n - m) := h2.trans h1
    have hkpos : 0 < (n - m : ℤ) := sub_pos.mpr hnm
    have : ρ' ≤ ρ := (zpow_le_zpow_iff_left₀ hρ'.le hρ.le hkpos).mp hleρ
    exact (not_le_of_gt hρρ') this
  unfold highIndex lowIndex
  exact csSup_le hAne fun n hn => le_csInf hBne fun m hm => hcmp n hn m hm
