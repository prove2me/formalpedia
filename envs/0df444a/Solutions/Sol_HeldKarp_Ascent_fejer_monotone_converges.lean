-- Prove2me | solution 1 for HeldKarp.Ascent.fejer_monotone_converges
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:43:47.240987+00:00
-- url     : https://prove2.me/submissions/5b017536-3cad-4a68-8ecf-686ebec6f943

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic
open Filter Topology
open scoped BigOperators
noncomputable section

theorem _root_.solution {d : ℕ} (A : Set (Fin d → ℝ)) (hA : (interior A).Nonempty)
    (y : ℕ → Fin d → ℝ) (hy : ∀ x ∈ A, Antitone (fun m => ∑ i, (y m i - x i) ^ 2)) :
    ∃ p : Fin d → ℝ, Tendsto y atTop (𝓝 p) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let Q (x : Fin d → ℝ) (m : ℕ) := ∑ i, (y m i - x i)^2
  have hQ (x : Fin d → ℝ) (hx : x ∈ A) : Tendsto (Q x) atTop (𝓝 (⨅ m, Q x m)) := by
    apply tendsto_atTop_ciInf (hy x hx)
    exact ⟨0, by rintro _ ⟨m, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩
  have haA : a ∈ A := interior_subset ha
  have hcoord (i : Fin d) : ∃ p : ℝ, Tendsto (fun m => y m i) atTop (𝓝 p) := by
    let x (j : Fin d) := a j + if j = i then r/2 else 0
    have hx : x ∈ A := by
      apply hball
      apply (dist_pi_lt_iff hr).2
      intro j
      dsimp [x]
      by_cases hji : j = i
      · simp [hji, Real.dist_eq, abs_of_pos hr]
        linarith
      · simp [hji, hr]
    have heq (m : ℕ) : Q x m - Q a m = -r * (y m i - a i) + (r/2)^2 := by
      change (∑ j, (y m j - x j)^2) - (∑ j, (y m j - a j)^2) = _
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp only [x, ite_true, ite_self, eq_self]
        ring
      · intro j _ hji
        simp [x, hji]
      · simp
    have hid (m : ℕ) : y m i = a i + ((r/2)^2 - (Q x m - Q a m))/r := by
      have hh := heq m
      field_simp [hr.ne']
      nlinarith
    have ht : Tendsto (fun m => a i + ((r/2)^2 - (Q x m - Q a m))/r) atTop
        (𝓝 (a i + ((r/2)^2 - ((⨅ m, Q x m) - (⨅ m, Q a m)))/r)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.sub ((hQ x hx).sub (hQ a haA))).div_const r)
    refine ⟨a i + ((r/2)^2 - ((⨅ m, Q x m) - (⨅ m, Q a m)))/r, ?_⟩
    simpa only [← hid] using ht
  choose p hp using hcoord
  exact ⟨p, tendsto_pi_nhds.mpr hp⟩
