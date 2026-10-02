-- Prove2me | solution 1 for MilnorDynamics.locally_bounded_subseq_locally_uniform
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:51:05.925684+00:00
-- url     : https://prove2.me/submissions/21b966be-811a-4abb-8768-3180c445ef7b

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace Cex5b631010

/-- Tent functions: `1` at the origin, supported in the disc of radius `1/n`. -/
noncomputable def tent (n : ℕ) (z : ℂ) : ℂ := ((max 0 (1 - (n : ℝ) * ‖z‖) : ℝ) : ℂ)

theorem tent_cont (n : ℕ) : Continuous (tent n) := by
  unfold tent
  fun_prop

theorem tent_bound (n : ℕ) (z : ℂ) : ‖tent n z‖ ≤ 1 := by
  unfold tent
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  apply max_le zero_le_one
  have : 0 ≤ (n : ℝ) * ‖z‖ := by positivity
  linarith

theorem tent_zero (n : ℕ) : tent n 0 = 1 := by
  simp [tent]

theorem tent_eventually (z : ℂ) (hz : z ≠ 0) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∀ᶠ n in atTop, tent (φ n) z = 0 := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  have h1 : (N : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hn.trans (hφ.id_le n)
  have h2 : 1 < (φ n : ℝ) * ‖z‖ := by
    rw [div_lt_iff₀ hpos] at hN
    nlinarith
  unfold tent
  rw [max_eq_left (by linarith)]
  simp

theorem cex : ¬ (∀ (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, ContinuousOn (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M),
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U) := by
  intro H
  obtain ⟨φ, hφ, g, hg, hT⟩ := H univ isOpen_univ tent
    (fun n => (tent_cont n).continuousOn)
    (fun K _ _ => ⟨1, fun n z _ => tent_bound n z⟩)
  have hgc : Continuous g := continuousOn_univ.mp hg
  have hlim : ∀ z, Tendsto (fun n => tent (φ n) z) atTop (nhds (g z)) :=
    fun z => hT.tendsto_at (mem_univ z)
  have hg0 : g 0 = 1 := by
    have := hlim 0
    simp only [tent_zero] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hgz : ∀ z, z ≠ 0 → g z = 0 := by
    intro z hz
    have h0 : Tendsto (fun n => tent (φ n) z) atTop (nhds 0) :=
      tendsto_const_nhds.congr' ((tent_eventually z hz φ hφ).mono fun n h => h.symm)
    exact tendsto_nhds_unique (hlim z) h0
  have hclosed : IsClosed {z : ℂ | g z = 0} := isClosed_eq hgc continuous_const
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {z : ℂ | g z = 0} := fun z hz => hgz z hz
  have hmem : (0 : ℂ) ∈ {z : ℂ | g z = 0} := by
    apply hclosed.closure_subset_iff.mpr hsub
    rw [dense_compl_singleton (0 : ℂ) |>.closure_eq]
    exact mem_univ _
  have : g 0 = 0 := hmem
  rw [hg0] at this
  exact one_ne_zero this

end Cex5b631010

theorem solution : ¬ (∀ (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, ContinuousOn (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M),
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U) := by
  exact Cex5b631010.cex
