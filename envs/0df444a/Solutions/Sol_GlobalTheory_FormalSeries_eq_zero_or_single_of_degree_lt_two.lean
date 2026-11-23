-- Prove2me | solution 1 for GlobalTheory.FormalSeries.eq_zero_or_single_of_degree_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:17.172809+00:00
-- url     : https://prove2.me/submissions/5aa2e710-cb21-45dc-a74b-29683999389c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution {d : σ →₀ ℕ} (hd : d.degree < 2) :
    d = 0 ∨ ∃ j, d = Finsupp.single j 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  right
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨j, ?_⟩
  have hdj : d j ≤ d.degree := Finsupp.le_degree j d
  have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
  ext i
  by_cases hij : i = j
  · rw [hij, Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hij)]
    by_contra hi
    have hsub : ({i, j} : Finset σ) ⊆ d.support := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finsupp.mem_support_iff.mpr hi
      · exact hj
    have hle := Finset.sum_le_sum_of_subset (f := fun x => d x) hsub
    rw [Finset.sum_pair hij, ← Finsupp.degree_apply] at hle
    omega
end GlobalTheory.FormalSeries
