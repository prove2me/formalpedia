-- Prove2me | solution 1 for Hirsch.tight_row_interval
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:40:40.067693+00:00
-- url     : https://prove2.me/submissions/c0338f65-954f-4f2e-8545-50542c30cc55

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Theorems.Thm_Hirsch_face_connected
import Theorems.Thm_Hirsch_gdist_reach

open scoped RealInnerProductSpace
open Hirsch

set_option autoImplicit false

namespace NumberHirschTightInterval

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem adj_right_mem_extremePoints {P : Set E} {a b : E} (h : Adj P a b) :
    b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1:ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1:ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      have h5 : p * s + q * t ≤ p * 1 + q * 1 := by
        have := hs.2; have := ht.2
        nlinarith
      nlinarith [hs.2, ht.2, hs.1, ht.1]
    rw [hs1]
    module
  have := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [this] at hb
  exact hb.2

private theorem reach_extend {P : Set E} {L : ℕ} {u x y : E}
    (hr : Reach P L u x) (hxy : x = y ∨ Adj P x y) :
    Reach P (L + 1) u y := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := hr
  refine ⟨fun i => if i ≤ L then w i else y, by simpa using h0, by simp, ?_⟩
  intro i hi
  rcases lt_or_ge i L with hil | hil
  · have hi1 : i + 1 ≤ L := hil
    simp only [if_pos hil.le, if_pos hi1]
    exact hstep i hil
  · have hiL : i = L := by omega
    subst i
    simpa [hL] using hxy

private theorem exists_index_of_le {f : ℕ → ℕ} {M t : ℕ} (h0 : f 0 ≤ t)
    (hstep : ∀ j < M, f (j + 1) ≤ f j + 1) (ht : t ≤ f M) :
    ∃ j ≤ M, f j = t := by
  induction M with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ M ih =>
      by_cases hle : t ≤ f M
      · obtain ⟨j, hjM, hj⟩ := ih (fun j hj => hstep j (by omega)) hle
        exact ⟨j, by omega, hj⟩
      · have := hstep M (by omega)
        exact ⟨M + 1, le_rfl, by omega⟩

end NumberHirschTightInterval

open NumberHirschTightInterval

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (s : Fin n) (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ Set.extremePoints ℝ (Hpoly a b)) (hq : q ∈ Set.extremePoints ℝ (Hpoly a b))
    (hps : ⟪a s, p⟫ = b s) (hqs : ⟪a s, q⟫ = b s)
    (t : ℕ) (hpt : gdist (Hpoly a b) u p ≤ t) (htq : t ≤ gdist (Hpoly a b) u q) :
    ∃ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a s, w⟫ = b s ∧ gdist (Hpoly a b) u w = t := by
  obtain ⟨L, w, hw0, hwL, hstep, htight⟩ := face_connected d n a b hbd p q hp hq
  have hvertex : ∀ k ≤ L, w k ∈ Set.extremePoints ℝ (Hpoly a b) := by
    intro k
    induction k with
    | zero => intro _; simpa [hw0] using hp
    | succ k ih =>
        intro hk
        rcases hstep k (by omega) with heq | hadj
        · rw [← heq]
          exact ih (by omega)
        · exact adj_right_mem_extremePoints hadj
  have hdist : ∀ k < L,
      gdist (Hpoly a b) u (w (k + 1)) ≤ gdist (Hpoly a b) u (w k) + 1 := by
    intro k hk
    have hr := gdist_reach d n a b hbd u (w k) hu (hvertex k (by omega))
    exact Nat.sInf_le (reach_extend hr (hstep k hk))
  obtain ⟨k, hk, hkt⟩ := exists_index_of_le
    (f := fun k => gdist (Hpoly a b) u (w k))
    (by simpa [hw0] using hpt) hdist (by simpa [hwL] using htq)
  exact ⟨w k, hvertex k hk, htight k hk s hps hqs, hkt⟩

#print axioms solution
