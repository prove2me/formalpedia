-- Prove2me | solution 1 for MegiddoLP.FixedDim.pair_opposite_slopes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:30:53.312913+00:00
-- url     : https://prove2.me/submissions/2275698a-24c7-44e1-80cb-4a193224a4a8

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

namespace MegiddoLP.FixedDim

theorem aux_pos_cmp_of_mul_pos {a b : ℝ} (h : 0 < a * b) : compare a 0 = compare b 0 := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [compare_gt_iff_gt.2 ha, compare_gt_iff_gt.2 hb]
  · rw [compare_lt_iff_lt.2 ha, compare_lt_iff_lt.2 hb]

theorem aux_pos_cmp_sub (a b : ℝ) : compare a b = compare (a - b) 0 := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (by linarith)]
  · subst h; simp
  · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2 (by linarith)]

/-- Representative real number of an ordering. -/
def aux_pos_toR : Ordering → ℝ
  | .lt => -1
  | .eq => 0
  | .gt => 1

theorem aux_pos_toR_spec (p : ℝ) :
    (p < 0 ∧ aux_pos_toR (compare p 0) = -1) ∨ (p = 0 ∧ aux_pos_toR (compare p 0) = 0) ∨
      (0 < p ∧ aux_pos_toR (compare p 0) = 1) := by
  rcases lt_trichotomy p 0 with h | h | h
  · left; exact ⟨h, by rw [compare_lt_iff_lt.2 h]; rfl⟩
  · right; left; exact ⟨h, by rw [compare_eq_iff_eq.2 h]; rfl⟩
  · right; right; exact ⟨h, by rw [compare_gt_iff_gt.2 h]; rfl⟩

theorem aux_pos_keyA (a0 a1 D p q u : ℝ) (hD : D ≠ 0) (ha : a0 * a1 ≤ 0)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0) (hu : D * u = a1 * p - a0 * q)
    (hc : compare p 0 = compare q 0 ∨ p = 0 ∨ q = 0) :
    compare u 0 =
      compare ((a1 * aux_pos_toR (compare p 0) - a0 * aux_pos_toR (compare q 0)) * D) 0 := by
  have hc' : aux_pos_toR (compare p 0) = aux_pos_toR (compare q 0) ∨ p = 0 ∨ q = 0 := by
    rcases hc with h | h | h
    · left; rw [h]
    · right; left; exact h
    · right; right; exact h
  have sp := aux_pos_toR_spec p
  have sq := aux_pos_toR_spec q
  generalize aux_pos_toR (compare p 0) = s at *
  generalize aux_pos_toR (compare q 0) = t at *
  have key : 0 < (a1 * s - a0 * t) * (a1 * p - a0 * q) ∨
      (a1 * s - a0 * t = 0 ∧ a1 * p - a0 * q = 0) := by
    have ha0 : 0 ≤ a0 ^ 2 := sq_nonneg _
    have ha1 : 0 ≤ a1 ^ 2 := sq_nonneg _
    have hpos : 0 < a0 ^ 2 + a1 ^ 2 := by
      rcases hne with h | h
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; linarith
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; linarith
    rcases sp with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ <;>
      rcases sq with ⟨hq, rfl⟩ | ⟨hq, rfl⟩ | ⟨hq, rfl⟩
    · left; nlinarith [mul_nonneg (neg_nonneg.2 ha) (neg_nonneg.2 hp.le),
        mul_nonneg (neg_nonneg.2 ha) (neg_nonneg.2 hq.le),
        mul_nonneg ha0 (neg_nonneg.2 hq.le), mul_nonneg ha1 (neg_nonneg.2 hp.le),
        mul_pos hpos (neg_pos.2 hp), mul_pos hpos (neg_pos.2 hq)]
    · subst hq
      by_cases h1 : a1 = 0
      · right; subst h1; constructor <;> ring
      · left; have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
        nlinarith [mul_pos this (neg_pos.2 hp)]
    · exfalso; rcases hc' with h | h | h
      · norm_num at h
      · linarith
      · linarith
    · subst hp
      by_cases h0 : a0 = 0
      · right; subst h0; constructor <;> ring
      · left; have := pow_pos (abs_pos.2 h0) 2; rw [sq_abs] at this
        nlinarith [mul_pos this (neg_pos.2 hq)]
    · subst hp; subst hq; right; constructor <;> ring
    · subst hp
      by_cases h0 : a0 = 0
      · right; subst h0; constructor <;> ring
      · left; have := pow_pos (abs_pos.2 h0) 2; rw [sq_abs] at this
        nlinarith [mul_pos this hq]
    · exfalso; rcases hc' with h | h | h
      · norm_num at h
      · linarith
      · linarith
    · subst hq
      by_cases h1 : a1 = 0
      · right; subst h1; constructor <;> ring
      · left; have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
        nlinarith [mul_pos this hp]
    · left; nlinarith [mul_nonneg (neg_nonneg.2 ha) hp.le,
        mul_nonneg (neg_nonneg.2 ha) hq.le,
        mul_nonneg ha0 hq.le, mul_nonneg ha1 hp.le,
        mul_pos hpos hp, mul_pos hpos hq]
  rcases key with h | ⟨h1, h2⟩
  · apply aux_pos_cmp_of_mul_pos
    have e : u * ((a1 * s - a0 * t) * D) = (a1 * s - a0 * t) * (D * u) := by ring
    rw [e, hu]; exact h
  · have hu0 : u = 0 := by
      rw [h2] at hu; exact (mul_eq_zero.1 hu).resolve_left hD
    rw [hu0, h1]; simp

theorem aux_pos_keyB (k0 k1 D p q v : ℝ) (hk : 0 ≤ k0 * k1) (hk1 : k1 ≠ 0)
    (hv : D * v = k1 * p - k0 * q)
    (hc : (p < 0 ∧ 0 < q) ∨ (0 < p ∧ q < 0)) :
    compare v 0 =
      compare ((k1 * aux_pos_toR (compare p 0) - k0 * aux_pos_toR (compare q 0)) * D) 0 := by
  have hk1' : 0 < k1 ^ 2 := by
    have := pow_pos (abs_pos.2 hk1) 2; rwa [sq_abs] at this
  have hk0 : 0 ≤ k0 ^ 2 := sq_nonneg _
  apply aux_pos_cmp_of_mul_pos
  rcases hc with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [compare_lt_iff_lt.2 hp, compare_gt_iff_gt.2 hq]
    have e : v * ((k1 * aux_pos_toR Ordering.lt - k0 * aux_pos_toR Ordering.gt) * D) =
        (-k1 - k0) * (D * v) := by simp [aux_pos_toR]; ring
    rw [e, hv]
    nlinarith [mul_pos hk1' (neg_pos.2 hp), mul_nonneg hk hq.le,
      mul_nonneg hk (neg_nonneg.2 hp.le), mul_nonneg hk0 hq.le]
  · rw [compare_gt_iff_gt.2 hp, compare_lt_iff_lt.2 hq]
    have e : v * ((k1 * aux_pos_toR Ordering.gt - k0 * aux_pos_toR Ordering.lt) * D) =
        (k1 + k0) * (D * v) := by simp [aux_pos_toR]; ring
    rw [e, hv]
    nlinarith [mul_pos hk1' hp, mul_nonneg hk (neg_nonneg.2 hq.le),
      mul_nonneg hk hp.le, mul_nonneg hk0 (neg_nonneg.2 hq.le)]

theorem aux_pos_dot1 {d : ℕ} (ai ak x : Fin (d + 2) → ℝ) :
    pairNormal1 ai ak ⬝ᵥ x = ak 0 * (ai ⬝ᵥ x) - ai 0 * (ak ⬝ᵥ x) := by
  simp only [pairNormal1, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem aux_pos_dot2 {d : ℕ} (ai ak x : Fin (d + 2) → ℝ) :
    pairNormal2 ai ak ⬝ᵥ x = ak 1 * (ai ⬝ᵥ x) - ai 1 * (ak ⬝ᵥ x) := by
  simp only [pairNormal2, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end MegiddoLP.FixedDim

open MegiddoLP.FixedDim

theorem solution {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak)
    (hdet : ak 0 * ai 1 - ak 1 * ai 0 ≠ 0) :
    ∃ F : Ordering → Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (pairNormal1 ai ak ⬝ᵥ x) (pairRhs1 ai ak bi bk))
                 (compare (pairNormal2 ai ak ⬝ᵥ x) (pairRhs2 ai ak bi bk))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by
  set D := ak 0 * ai 1 - ak 1 * ai 0 with hDdef
  -- slope facts
  have ha : ai 0 * ai 1 ≤ 0 := by
    rcases hi with h | h
    · rw [h]; simp
    · by_cases h1 : ai 1 = 0
      · rw [h1]; simp
      · have e : -(ai 0) / ai 1 * (ai 1) ^ 2 = -(ai 0 * ai 1) := by field_simp
        have := mul_nonneg h (sq_nonneg (ai 1))
        linarith
  have hkk : 0 ≤ ak 0 * ak 1 := by
    obtain ⟨h1, h2⟩ := hk
    have e : -(ak 0) / ak 1 * (ak 1) ^ 2 = -(ak 0 * ak 1) := by field_simp
    have := mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg (ak 1))
    linarith
  have hne : ai 0 ≠ 0 ∨ ai 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet; rw [hDdef, h.1, h.2]; ring
  refine ⟨fun o1 o2 => if (o1 = o2 ∨ o1 = Ordering.eq ∨ o2 = Ordering.eq) then
      (true, compare ((ai 1 * aux_pos_toR o1 - ai 0 * aux_pos_toR o2) * D) 0)
    else (false, compare ((ak 1 * aux_pos_toR o1 - ak 0 * aux_pos_toR o2) * D) 0), ?_⟩
  intro x
  set u := ai ⬝ᵥ x - bi with hu
  set v := ak ⬝ᵥ x - bk with hv
  have h1 : compare (pairNormal1 ai ak ⬝ᵥ x) (pairRhs1 ai ak bi bk) =
      compare (ak 0 * u - ai 0 * v) 0 := by
    rw [aux_pos_cmp_sub, aux_pos_dot1, pairRhs1]; congr 1; rw [hu, hv]; ring
  have h2 : compare (pairNormal2 ai ak ⬝ᵥ x) (pairRhs2 ai ak bi bk) =
      compare (ak 1 * u - ai 1 * v) 0 := by
    rw [aux_pos_cmp_sub, aux_pos_dot2, pairRhs2]; congr 1; rw [hu, hv]; ring
  have h3 : compare (ai ⬝ᵥ x) bi = compare u 0 := aux_pos_cmp_sub _ _
  have h4 : compare (ak ⬝ᵥ x) bk = compare v 0 := aux_pos_cmp_sub _ _
  dsimp only
  rw [h1, h2, h3, h4]
  set p := ak 0 * u - ai 0 * v with hp
  set q := ak 1 * u - ai 1 * v with hq
  have eu : D * u = ai 1 * p - ai 0 * q := by rw [hp, hq, hDdef]; ring
  have ev : D * v = ak 1 * p - ak 0 * q := by rw [hp, hq, hDdef]; ring
  split_ifs with hc
  · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    apply aux_pos_keyA (ai 0) (ai 1) D p q u hdet ha hne eu
    rcases hc with h | h | h
    · left; exact h
    · right; left; exact compare_eq_iff_eq.1 h
    · right; right; exact compare_eq_iff_eq.1 h
  · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    apply aux_pos_keyB (ak 0) (ak 1) D p q v hkk hk.1 ev
    push Not at hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    rcases lt_trichotomy p 0 with hp' | hp' | hp'
    · rcases lt_trichotomy q 0 with hq' | hq' | hq'
      · exact absurd (by rw [compare_lt_iff_lt.2 hp', compare_lt_iff_lt.2 hq']) hc1
      · exact absurd (compare_eq_iff_eq.2 hq') hc3
      · left; exact ⟨hp', hq'⟩
    · exact absurd (compare_eq_iff_eq.2 hp') hc2
    · rcases lt_trichotomy q 0 with hq' | hq' | hq'
      · right; exact ⟨hp', hq'⟩
      · exact absurd (compare_eq_iff_eq.2 hq') hc3
      · exact absurd (by rw [compare_gt_iff_gt.2 hp', compare_gt_iff_gt.2 hq']) hc1
