-- Prove2me | solution 1 for GeomScoring.Characterization.geometric_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:10:28.732689+00:00
-- url     : https://prove2.me/submissions/98cad985-1d6b-4b02-9ffd-cac2d2e790f6

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

open GeomScoring.Characterization

namespace GSGeoRec

lemma geom_rec (p : ℝ) (m j : ℕ) (hj : j + 1 < m) :
    geomScore p m ⟨j, by omega⟩ = p * geomScore p m ⟨j+1, hj⟩
      + (if 1 < p then 0 else if p = 1 then 1 else 1 - p) := by
  have he : m - 1 - j = (m - 1 - (j+1)) + 1 := by omega
  simp only [geomScore]
  rw [he]
  split_ifs with h1 h2
  · ring
  · subst h2; push_cast; ring
  · ring

lemma geom_last2 (p : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    geomScore p m ⟨m-1, by omega⟩ < geomScore p m ⟨m-2, by omega⟩ := by
  have e1 : m - 1 - (m - 1) = 0 := by omega
  have e2 : m - 1 - (m - 2) = 1 := by omega
  simp only [geomScore, e1, e2]
  split_ifs with h1 h2
  · simpa using h1
  · simp
  · have : p < 1 := lt_of_le_of_ne (not_lt.mp h1) h2
    simp; linarith

end GSGeoRec

open GSGeoRec in
theorem solution (m : ℕ) (v : Fin m → ℝ) (hv : StrictAnti v)
    (h : AffEquiv (initSeg v (m - 1)) (finalSeg v (m - 1))) :
    ∃ p : ℝ, 0 < p ∧ AffEquiv v (geomScore p m) := by
  by_cases hm : m < 2
  · refine ⟨1, one_pos, ?_⟩
    interval_cases m
    · exact ⟨1, 0, one_pos, fun j => j.elim0⟩
    · exact ⟨1, v 0 - geomScore 1 1 0, one_pos, fun j => by fin_cases j; simp⟩
  replace hm : 2 ≤ m := by omega
  obtain ⟨a, b, ha, hab⟩ := h
  have hrec : ∀ j (hj : j + 1 < m), v ⟨j, by omega⟩ = a * v ⟨j+1, hj⟩ + b := by
    intro j hj
    have := hab ⟨j, by omega⟩
    simp only [initSeg, finalSeg] at this
    rw [dif_pos (by omega), dif_pos (by omega)] at this
    have e : j + (m - (m - 1)) = j + 1 := by omega
    simp only [e] at this
    exact this
  refine ⟨a, ha, ?_⟩
  set g := geomScore a m with hg
  set c : ℝ := (if 1 < a then 0 else if a = 1 then 1 else 1 - a) with hc
  have grec : ∀ j (hj : j + 1 < m), g ⟨j, by omega⟩ = a * g ⟨j+1, hj⟩ + c :=
    fun j hj => geom_rec a m j hj
  have hG := geom_last2 a m hm
  have hV : v ⟨m-1, by omega⟩ < v ⟨m-2, by omega⟩ := hv (by simp [Fin.lt_def]; omega)
  set G := g ⟨m-2, by omega⟩ - g ⟨m-1, by omega⟩ with hGdef
  have Gpos : 0 < G := by rw [hGdef]; linarith
  set A := (v ⟨m-2, by omega⟩ - v ⟨m-1, by omega⟩) / G with hA
  have Apos : 0 < A := div_pos (by linarith) Gpos
  set B := v ⟨m-1, by omega⟩ - A * g ⟨m-1, by omega⟩ with hB
  have P1 : v ⟨m-2, by omega⟩ = A * g ⟨m-2, by omega⟩ + B := by
    rw [hB, hA]
    field_simp
    rw [hGdef]; ring
  have hb : b = A * c + B - a * B := by
    have e1 := hrec (m-2) (by omega)
    have e2 := grec (m-2) (by omega)
    have e3 : (⟨m - 2 + 1, by omega⟩ : Fin m) = ⟨m-1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e3] at e1 e2
    have : b = v ⟨m-2, by omega⟩ - a * v ⟨m-1, by omega⟩ := by linarith
    rw [this, P1, e2, hB]; ring
  have key : ∀ t j (hj : j < m), m - 1 - j = t → v ⟨j, hj⟩ = A * g ⟨j, hj⟩ + B := by
    intro t
    induction t with
    | zero =>
      intro j hj hjt
      have : j = m - 1 := by omega
      subst this
      rw [hB]; ring
    | succ t ih =>
      intro j hj hjt
      have hj1 : j + 1 < m := by omega
      rw [hrec j hj1, grec j hj1, ih (j+1) hj1 (by omega), hb]
      ring
  exact ⟨A, B, Apos, fun j => key _ j.1 j.2 rfl⟩
