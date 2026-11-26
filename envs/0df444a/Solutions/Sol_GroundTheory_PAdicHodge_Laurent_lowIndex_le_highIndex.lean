-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.lowIndex_le_highIndex
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:45:36.099381+00:00
-- url     : https://prove2.me/submissions/f85f8377-9bec-4e6b-8f1c-3902da41df67

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
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem solution : lowIndex a ρ ≤ highIndex a ρ := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at hε
  have hbdd : BddAbove (Set.range f) := by
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
  have hpos : 0 < ⨆ n, f n := by
    obtain ⟨n, hn⟩ : ∃ n, a n ≠ 0 := by
      contrapose! ha
      exact funext ha
    have : 0 < f n := mul_pos (norm_pos_iff.mpr hn) (zpow_pos hρ n)
    exact this.trans_le (le_ciSup hbdd n)
  set M := ⨆ n, f n
  have hgauss : gaussNorm a ρ = M := rfl
  have hdom : (domSet a ρ).Nonempty := by
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
      linarith [hpos]
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
  have hfin : (domSet a ρ).Finite := by
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
  unfold lowIndex highIndex
  exact csInf_le_csSup hdom hfin.bddBelow hfin.bddAbove
