-- Prove2me | solution 1 for GravesWillems.Serial.no_stage_one_backlog
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:24:35.504112+00:00
-- url     : https://prove2.me/submissions/6dc8f126-8182-4db9-85d5-8d6bbbd33309

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

theorem aux_nsob_window_add (d : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    windowDemand d a b + windowDemand d b c = windowDemand d a c := by
  unfold windowDemand
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.sum_union]
  exact Finset.Ioc_disjoint_Ioc_of_le le_rfl

theorem aux_nsob_window_self (d : ℤ → ℝ) (a : ℤ) : windowDemand d a a = 0 := by
  unfold windowDemand
  simp

theorem aux_nsob_nonneg (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (r i : ℕ) (t : ℤ) :
    0 ≤ backlogAux T B d r i t := by
  cases r with
  | zero => simp [backlogAux]
  | succ r => simp only [backlogAux]; exact le_max_left _ _

theorem aux_nsob_prefix (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) (d : ℤ → ℝ)
    (hdD : ∀ (a : ℤ) (s : ℕ), windowDemand d a (a + (s : ℤ)) ≤ D s)
    (hB : ServiceConstraints N T D B) (k : ℕ) (hk : k ≤ N) (t0 : ℤ) :
    windowDemand d (t0 - ((∑ m ∈ Finset.Icc 1 k, T m : ℕ) : ℤ)) t0
      ≤ ∑ m ∈ Finset.Icc 1 k, B m := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp [aux_nsob_window_self]
  · have h1 := hdD (t0 - ((∑ m ∈ Finset.Icc 1 k, T m : ℕ) : ℤ)) (∑ m ∈ Finset.Icc 1 k, T m)
    have h2 := hB k (Finset.mem_Icc.mpr ⟨hpos, hk⟩)
    simp only [sub_add_cancel] at h1
    linarith

theorem aux_nsob_main (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) (d : ℤ → ℝ)
    (hdD : ∀ (a : ℤ) (s : ℕ), windowDemand d a (a + (s : ℤ)) ≤ D s)
    (hB : ServiceConstraints N T D B) :
    ∀ r k : ℕ, k + r = N → ∀ t0 : ℤ,
      windowDemand d (t0 - ((∑ m ∈ Finset.Icc 1 k, T m : ℕ) : ℤ)) t0
        + backlogAux T B d r (k + 1) (t0 - ((∑ m ∈ Finset.Icc 1 k, T m : ℕ) : ℤ))
        ≤ ∑ m ∈ Finset.Icc 1 k, B m := by
  intro r
  induction r with
  | zero =>
    intro k hk t0
    simp only [backlogAux, add_zero]
    exact aux_nsob_prefix N T D B d hdD hB k (by omega) t0
  | succ r ih =>
    intro k hk t0
    have hIH := ih (k + 1) (by omega) t0
    have hS : (∑ m ∈ Finset.Icc 1 (k + 1), T m) = (∑ m ∈ Finset.Icc 1 k, T m) + T (k + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hP : (∑ m ∈ Finset.Icc 1 (k + 1), B m) = (∑ m ∈ Finset.Icc 1 k, B m) + B (k + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hpre := aux_nsob_prefix N T D B d hdD hB k (by omega) t0
    set S := (∑ m ∈ Finset.Icc 1 k, T m) with hSdef
    set P := (∑ m ∈ Finset.Icc 1 k, B m) with hPdef
    have ht : t0 - (S : ℤ) - ((T (k + 1) : ℕ) : ℤ) = t0 - ((S + T (k + 1) : ℕ) : ℤ) := by
      push_cast; ring
    rw [hS, hP] at hIH
    simp only [backlogAux]
    rw [ht]
    have hTnn : (0 : ℤ) ≤ ((T (k + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    have hSnn : (0 : ℤ) ≤ ((S : ℕ) : ℤ) := Int.natCast_nonneg _
    have hadd := aux_nsob_window_add d
      (a := t0 - ((S + T (k + 1) : ℕ) : ℤ)) (b := t0 - (S : ℤ)) (c := t0)
      (by push_cast; linarith) (by linarith)
    rcases le_total 0 (windowDemand d (t0 - ((S + T (k + 1) : ℕ) : ℤ)) (t0 - (S : ℤ))
        + backlogAux T B d r (k + 1 + 1) (t0 - ((S + T (k + 1) : ℕ) : ℤ)) - B (k + 1))
      with hc | hc
    · rw [max_eq_right hc]
      linarith
    · rw [max_eq_left hc]
      linarith

end GravesWillems.Serial

open GravesWillems.Serial

theorem solution (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) (d : ℤ → ℝ)
    (hdD : ∀ (a : ℤ) (s : ℕ), windowDemand d a (a + (s : ℤ)) ≤ D s)
    (hB : ServiceConstraints N T D B) (t : ℤ) :
    backlog N T B d 1 t = 0 := by
  have h := aux_nsob_main N T D B d hdD hB N 0 (by omega) t
  simp [aux_nsob_window_self] at h
  have hnn := aux_nsob_nonneg T B d N 1 t
  unfold backlog
  have hN : N + 1 - 1 = N := by omega
  rw [hN]
  linarith
