-- Prove2me | solution 1 for KarpPapadimitriou.SmallFacial.zero_one_vertices
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:26:16.793437+00:00
-- url     : https://prove2.me/submissions/91bec285-33a9-4591-90a5-2b9141b2cccb

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP



namespace KarpPapadimitriou.SmallFacial

theorem zo_core (C : COP) (hC : IsZeroOne C) (z : List Bool) (hz : z ∈ C.L) :
    (∀ v, IsVertex (hull C z) v → ∀ i, v i = 0 ∨ v i = 1) ∧
    ¬ HasRay (hull C z) := by
  set T : Set (Fin (C.n z) → ℚ) := {x | ∃ y ∈ C.S z, x = fun i => (y i : ℚ)} with hT
  have hTcube : ∀ x ∈ T, ∀ i, x i = 0 ∨ x i = 1 := by
    rintro x ⟨y, hy, rfl⟩ i
    rcases hC z hz y hy i with h | h <;> simp [h]
  have hcube : hull C z ⊆ {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    apply convexHull_min
    · intro x hx i
      rcases hTcube x hx i with h | h <;> simp [h]
    · intro x hx y hy a b ha hb hab i
      have h1 := hx i
      have h2 := hy i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  constructor
  · intro v hv i
    have hv' : v ∈ Set.extremePoints ℚ (hull C z) := by
      rw [mem_extremePoints]
      refine ⟨hv.1, ?_⟩
      intro a ha b hb hs
      obtain ⟨p, q, hp, hq, hpq, hab⟩ := hs
      have hq' : q = 1 - p := by linarith
      have := hv.2 a ha b hb p hp (by linarith) (by rw [← hq']; exact hab.symm)
      exact this
    have : v ∈ T := extremePoints_convexHull_subset hv'
    exact hTcube v this i
  · rintro ⟨v, d, hv, hd, hray⟩
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (funext h)
    have hvi := hcube hv i
    have hpos : 0 < |d i| := abs_pos.mpr hi
    have := hcube (hray (2 / |d i|) (by positivity)) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have key : 2 / |d i| * d i = 2 ∨ 2 / |d i| * d i = -2 := by
      rcases lt_or_gt_of_ne hi with h | h
      · right; rw [abs_of_neg h]; field_simp
      · left; rw [abs_of_pos h]; field_simp
    rcases key with k | k <;> rw [k] at this <;> linarith [this.1, this.2, hvi.1, hvi.2]

end KarpPapadimitriou.SmallFacial

open KarpPapadimitriou.SmallFacial


theorem solution (C : COP) (hC : IsZeroOne C) (z : List Bool) (hz : z ∈ C.L) :
    (∀ v, IsVertex (hull C z) v → ∀ i, v i = 0 ∨ v i = 1) ∧
    ¬ HasRay (hull C z) := by
  exact zo_core C hC z hz
