-- Prove2me | solution 1 for MovementSorting.Exponent.fact_3_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:58:37.603083+00:00
-- url     : https://prove2.me/submissions/09f665a5-8fc9-47d1-9cbd-e1fd82df98c8

import Definitions.Def_MovementSorting_Exponent_Geometry

set_option autoImplicit false

namespace MovementSorting.Exponent

lemma pl_cons_cons {Y : Type*} [MetricSpace Y] (x y : Y) (t : List Y) :
    pathLength (x :: y :: t) = dist x y + pathLength (y :: t) := by
  simp [pathLength, List.zip_cons_cons]

lemma pl_single {Y : Type*} [MetricSpace Y] (x : Y) : pathLength [x] = 0 := by
  simp [pathLength]

lemma pl_nonneg {Y : Type*} [MetricSpace Y] (s : List Y) : 0 ≤ pathLength s := by
  unfold pathLength
  apply List.sum_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨p, -, rfl⟩ := ha
  exact dist_nonneg

lemma pl_drop {Y : Type*} [MetricSpace Y] (x a : Y) (t : List Y) :
    pathLength (x :: t) ≤ dist x a + pathLength (a :: t) := by
  cases t with
  | nil => simp [pl_single, dist_nonneg]
  | cons b t' =>
    rw [pl_cons_cons, pl_cons_cons]
    linarith [dist_triangle x a b]

lemma pl_tail {Y : Type*} [MetricSpace Y] (x : Y) (t : List Y) :
    pathLength t ≤ pathLength (x :: t) := by
  cases t with
  | nil => simp [pathLength]
  | cons b t' => rw [pl_cons_cons]; linarith [dist_nonneg (x := x) (y := b)]

lemma claim {Y : Type*} [MetricSpace Y] [DecidableEq Y] (W0 : Finset Y) (h : Y → ℝ)
    (hpos : ∀ w, 0 ≤ h w)
    (H : ∀ w ∈ W0, ∀ w' ∈ W0, w ≠ w' → h w + h w' ≤ dist w w') :
    ∀ (s : List Y) (x : Y) (W : Finset Y), x ∈ W0 → W ⊆ W0 → x ∉ W → W.Nonempty →
      (∀ w ∈ W, w ∈ s) → h x + ∑ w ∈ W, h w ≤ pathLength (x :: s) := by
  intro s
  induction s with
  | nil =>
    intro x W _ _ _ hne hs
    obtain ⟨w, hw⟩ := hne
    simpa using hs w hw
  | cons a t ih =>
    intro x W hx hW hxW hne hs
    rw [pl_cons_cons]
    by_cases ha : a ∈ W
    · have hxa : x ≠ a := fun e => hxW (e ▸ ha)
      have hd := H x hx a (hW ha) hxa
      rw [← Finset.add_sum_erase W h ha]
      by_cases hne' : (W.erase a).Nonempty
      · have := ih a (W.erase a) (hW ha) ((Finset.erase_subset _ _).trans hW)
          (by simp) hne' (by
            intro w hw
            have hwa := Finset.ne_of_mem_erase hw
            rcases List.mem_cons.mp (hs w (Finset.mem_of_mem_erase hw)) with e | e
            · exact absurd e hwa
            · exact e)
        linarith [hpos a]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne']
        simp
        linarith [pl_nonneg (a :: t)]
    · have := ih x W hx hW hxW hne (by
        intro w hw
        rcases List.mem_cons.mp (hs w hw) with e | e
        · exact absurd (e ▸ hw) ha
        · exact e)
      linarith [pl_drop x a t]

end MovementSorting.Exponent

open MovementSorting.Exponent

theorem solution {Y : Type*} [MetricSpace Y] [DecidableEq Y] (W : Finset Y) (hW : 2 ≤ W.card)
    (s : List Y) (hs : ∀ w ∈ W, w ∈ s) :
    (1 / 2 : ℝ) * ∑ w ∈ W, nnDist W w ≤ pathLength s := by
  set h : Y → ℝ := fun w => (1 / 2 : ℝ) * nnDist W w with hh
  have hnn : ∀ w, 0 ≤ nnDist W w := by
    intro w
    unfold nnDist
    split_ifs with hne
    · exact Finset.le_inf' _ _ (fun _ _ => dist_nonneg)
    · exact le_refl _
  have hle : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → nnDist W w ≤ dist w w' := by
    intro w _ w' hw' hne
    have hm : w' ∈ W.erase w := Finset.mem_erase.mpr ⟨Ne.symm hne, hw'⟩
    unfold nnDist
    rw [dif_pos ⟨w', hm⟩]
    exact Finset.inf'_le _ hm
  have hpos : ∀ w, 0 ≤ h w := fun w => by simp only [hh]; linarith [hnn w]
  have H : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → h w + h w' ≤ dist w w' := by
    intro w hw w' hw' hne
    have h1 := hle w hw w' hw' hne
    have h2 := hle w' hw' w hw (Ne.symm hne)
    rw [dist_comm] at h2
    simp only [hh]; linarith
  rw [Finset.mul_sum]
  change ∑ w ∈ W, h w ≤ pathLength s
  clear_value h
  induction s with
  | nil =>
    exfalso
    have : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by simpa using hs w hw)
    simp [this] at hW
  | cons x t ih =>
    by_cases hc : x ∈ W ∧ x ∉ t
    · obtain ⟨hxW, hxt⟩ := hc
      rw [← Finset.add_sum_erase W h hxW]
      have hne : (W.erase x).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hxW]; omega
      exact claim W h hpos H t x (W.erase x) hxW (Finset.erase_subset _ _) (by simp) hne (by
        intro w hw
        rcases List.mem_cons.mp (hs w (Finset.mem_of_mem_erase hw)) with e | e
        · exact absurd e (Finset.ne_of_mem_erase hw)
        · exact e)
    · have ht : ∀ w ∈ W, w ∈ t := by
        intro w hw
        rcases List.mem_cons.mp (hs w hw) with e | e
        · subst e
          by_contra hn
          exact hc ⟨hw, hn⟩
        · exact e
      exact (ih ht).trans (pl_tail x t)
