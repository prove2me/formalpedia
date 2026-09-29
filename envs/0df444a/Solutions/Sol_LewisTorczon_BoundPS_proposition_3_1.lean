-- Prove2me | solution 1 for LewisTorczon.BoundPS.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:17:53.498458+00:00
-- url     : https://prove2.me/submissions/26294bc3-e76c-443c-92e0-77989ff46c15

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

lemma aux_pq31_clamp_coe {a b : EReal} {x : ℝ} (hax : a ≤ (x : EReal)) (hxb : (x : EReal) ≤ b)
    (y : ℝ) : ((clampCoord a b y : ℝ) : EReal) = max a (min b (y : EReal)) := by
  unfold clampCoord
  apply EReal.coe_toReal
  · exact (max_lt (lt_of_le_of_lt hax (EReal.coe_lt_top x))
      (lt_of_le_of_lt (min_le_right _ _) (EReal.coe_lt_top y))).ne
  · exact (lt_max_of_lt_right (lt_min (lt_of_lt_of_le (EReal.bot_lt_coe x) hxb)
      (EReal.bot_lt_coe y))).ne'

lemma aux_pq31_clamp_mem {a b : EReal} {x : ℝ} (hax : a ≤ (x : EReal)) (hxb : (x : EReal) ≤ b)
    (y : ℝ) : a ≤ ((clampCoord a b y : ℝ) : EReal) ∧ ((clampCoord a b y : ℝ) : EReal) ≤ b := by
  rw [aux_pq31_clamp_coe hax hxb]
  exact ⟨le_max_left _ _, max_le (hax.trans hxb) (min_le_left _ _)⟩

lemma aux_pq31_clamp_vi {a b : EReal} {x : ℝ} (hax : a ≤ (x : EReal)) (hxb : (x : EReal) ≤ b)
    (y t : ℝ) (hat : a ≤ (t : EReal)) (htb : (t : EReal) ≤ b) :
    (y - clampCoord a b y) * (t - clampCoord a b y) ≤ 0 := by
  have hc := aux_pq31_clamp_coe hax hxb y
  generalize clampCoord a b y = c at hc ⊢
  rcases lt_trichotomy y c with h | h | h
  · have hca : (c : EReal) = a := by
      rcases le_total a (min b (y : EReal)) with h1 | h1
      · rw [max_eq_right h1] at hc
        have : (c : EReal) ≤ y := hc ▸ min_le_right _ _
        exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr h)
      · rw [max_eq_left h1] at hc; exact hc
    have htc : c ≤ t := by rw [← EReal.coe_le_coe_iff, hca]; exact hat
    nlinarith
  · have : y - c = 0 := sub_eq_zero.mpr h
    rw [this, zero_mul]
  · have hcb : (c : EReal) = b := by
      rcases le_total b (y : EReal) with h1 | h1
      · rw [min_eq_left h1, max_eq_right (hax.trans hxb)] at hc; exact hc
      · rw [min_eq_right h1] at hc
        have : (y : EReal) ≤ c := hc ▸ le_max_right _ _
        exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr h)
    have htc : t ≤ c := by rw [← EReal.coe_le_coe_iff, hcb]; exact htb
    nlinarith

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n : ℕ} (lo hi : Fin n → EReal) (hlohi : ∀ j, lo j < hi j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi) :
    ‖projQ lo hi f x‖ ≤ ‖gradient f x‖ ∧ (IsStationary lo hi f x ↔ projQ lo hi f x = 0) := by
  set g := gradient f x with hg
  have hq : ∀ j, (projQ lo hi f x) j = clampCoord (lo j) (hi j) (x j - g j) - x j := by
    intro j
    simp [projQ, boxProj, hg]
  have key : ∀ j (t : ℝ), lo j ≤ (t : EReal) → (t : EReal) ≤ hi j →
      (x j - g j - clampCoord (lo j) (hi j) (x j - g j)) *
        (t - clampCoord (lo j) (hi j) (x j - g j)) ≤ 0 :=
    fun j t h1 h2 => aux_pq31_clamp_vi (hx j).1 (hx j).2 _ t h1 h2
  refine ⟨?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hq]
    have := key j (x j) (hx j).1 (hx j).2
    nlinarith
  · constructor
    · rintro ⟨_, hst⟩
      ext j
      rw [hq]
      simp only [PiLp.zero_apply]
      have hmem := aux_pq31_clamp_mem (hx j).1 (hx j).2 (x j - g j)
      have hk := key j (x j) (hx j).1 (hx j).2
      generalize clampCoord (lo j) (hi j) (x j - g j) = c at hmem hk
      set z : EuclideanSpace ℝ (Fin n) := x + EuclideanSpace.single j (c - x j) with hzdef
      have hz : z ∈ box lo hi := by
        intro i
        by_cases hij : i = j
        · subst hij
          simp [hzdef]
          exact hmem
        · simp [hzdef, hij]
          exact hx i
      have h1 := hst z hz
      rw [hzdef, add_sub_cancel_left, EuclideanSpace.inner_single_right] at h1
      simp only [conj_trivial] at h1
      nlinarith
    · intro h0
      refine ⟨hx, fun z hz => ?_⟩
      rw [PiLp.inner_apply]
      apply Finset.sum_nonneg
      intro j _
      have hj : (projQ lo hi f x) j = 0 := by rw [h0]; rfl
      rw [hq, sub_eq_zero] at hj
      have := key j (z j) (hz j).1 (hz j).2
      rw [hj] at this
      simp only [Real.inner_apply, PiLp.sub_apply]
      nlinarith
