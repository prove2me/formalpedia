-- Prove2me | solution 1 for MartOT.Card.local_sign
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:14:15.887984+00:00
-- url     : https://prove2.me/submissions/23c66c21-67b0-4437-9c04-0a9fdb52ea85

import Mathlib

namespace Aux_MOT_ls

lemma aux1 (t k M : ℝ) (ht : 0 ≤ t) (hk : 0 ≤ k) (h : t * (8 * (k + 1)) < M) :
    t * k < M / 8 := by nlinarith

lemma aux2 (t b c M : ℝ) (hb : 0 < b) (h : t * b * c < b * M) : t * c < M := by
  have : b * (t * c) < b * M := by linarith [show t * b * c = b * (t * c) by ring]
  exact lt_of_mul_lt_mul_left this hb.le

lemma aux3 (d1 d2 d3 w lam η : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) (h1 : |d1| < η)
    (h2 : |d2| < η) (h3 : |d3| < η) (hw : |w| < η) :
    |d1 - lam * d2 - (1 - lam) * d3 - w| < 4 * η := by
  obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
  obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
  obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
  obtain ⟨hwa, hwb⟩ := abs_lt.mp hw
  rw [abs_lt]
  constructor
  · nlinarith [mul_pos hl0 (by linarith : (0:ℝ) < η - d2),
      mul_pos (by linarith : (0:ℝ) < 1 - lam) (by linarith : (0:ℝ) < η - d3)]
  · nlinarith [mul_pos hl0 (by linarith : (0:ℝ) < η + d2),
      mul_pos (by linarith : (0:ℝ) < 1 - lam) (by linarith : (0:ℝ) < η + d3)]

lemma aux4 (E D : ℝ) (hD : D ≠ 0) (h : |E - D| < |D| / 2) : 0 < E * D := by
  have h1 : -(|E - D| * |D|) ≤ (E - D) * D := by rw [← abs_mul]; exact neg_abs_le _
  have h2 : D * D = |D| * |D| := (abs_mul_abs_self D).symm
  have h3 : 0 < |D| := abs_pos.mpr hD
  nlinarith [abs_nonneg (E - D)]

end Aux_MOT_ls

open Aux_MOT_ls in
theorem solution (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (a b0 bk bi : ℝ)
    (h0i : b0 < bi) (hik : bi < bk)
    (hD : deriv h (bi - a) -
        ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
          (bi - b0) / (bk - b0) * deriv h (bk - a)) ≠ 0) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ β a' : ℝ, |bi - β| < ε₁ → 0 < |a - a'| → |a - a'| < ε₁ →
      0 < ((h (β - a) + (β - b0) / (bk - b0) * h (bk - a') +
              (1 - (β - b0) / (bk - b0)) * h (b0 - a')) -
            (h (β - a') + (β - b0) / (bk - b0) * h (bk - a) +
              (1 - (β - b0) / (bk - b0)) * h (b0 - a))) *
          ((deriv h (bi - a) -
              ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
                (bi - b0) / (bk - b0) * deriv h (bk - a))) * (a' - a)) := by
  obtain ⟨D, hDd⟩ : ∃ D, D = deriv h (bi - a) -
        ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
          (bi - b0) / (bk - b0) * deriv h (bk - a)) := ⟨_, rfl⟩
  rw [← hDd] at hD ⊢
  have hbk : 0 < bk - b0 := by linarith
  have hcont : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have mvt : ∀ x y : ℝ, ∃ c, |c - x| ≤ |y - x| ∧ h y - h x = deriv h c * (y - x) := by
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope h hxy hdiff.continuous.continuousOn
        hdiff.differentiableOn
      refine ⟨c, ?_, ?_⟩
      · rw [abs_of_pos (by linarith [hc.1] : 0 < c - x), abs_of_pos (by linarith : 0 < y - x)]
        linarith [hc.2]
      · rw [hd, div_mul_cancel₀ _ (by linarith : y - x ≠ 0)]
    · exact ⟨x, by simp, by simp⟩
    · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope h hxy hdiff.continuous.continuousOn
        hdiff.differentiableOn
      refine ⟨c, ?_, ?_⟩
      · rw [abs_of_neg (by linarith [hc.2] : c - x < 0), abs_of_neg (by linarith : y - x < 0)]
        linarith [hc.1]
      · rw [hd]
        have : x - y ≠ 0 := by linarith
        field_simp
        ring
  obtain ⟨M, hMd⟩ : ∃ M, M = |D| := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMd]; exact abs_pos.mpr hD
  have hη : 0 < M / 8 := by positivity
  obtain ⟨δ1, hδ1, H1⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := bi - a)) _ hη
  obtain ⟨δ2, hδ2, H2⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := bk - a)) _ hη
  obtain ⟨δ3, hδ3, H3⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := b0 - a)) _ hη
  obtain ⟨K, hKd⟩ : ∃ K, K = deriv h (bk - a) - deriv h (b0 - a) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = min δ1 (min δ2 δ3) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδd]; exact lt_min hδ1 (lt_min hδ2 hδ3)
  have hδ1' : δ ≤ δ1 := by rw [hδd]; exact min_le_left _ _
  have hδ2' : δ ≤ δ2 := by rw [hδd]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3' : δ ≤ δ3 := by rw [hδd]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hK1 : 0 < 8 * (|K| + 1) := by positivity
  have hε4 : 0 < (bk - b0) * M / (8 * (|K| + 1)) := by positivity
  refine ⟨min (min (bi - b0) (bk - bi)) (min (δ / 2) ((bk - b0) * M / (8 * (|K| + 1)))),
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) hε4), ?_⟩
  intro β a' hβ ha0 ha1
  simp only [lt_min_iff] at hβ ha1
  obtain ⟨⟨hβ1, hβ2⟩, hβ3, hβ4⟩ := hβ
  obtain ⟨-, ha3, -⟩ := ha1
  have hβa := abs_lt.mp hβ1
  have hβb := abs_lt.mp hβ2
  have hβc := abs_lt.mp hβ3
  have haa := abs_lt.mp ha3
  obtain ⟨c1, hc1, e1⟩ := mvt (β - a) (β - a')
  obtain ⟨c2, hc2, e2⟩ := mvt (bk - a) (bk - a')
  obtain ⟨c3, hc3, e3⟩ := mvt (b0 - a) (b0 - a')
  have s1 : β - a' - (β - a) = a - a' := by ring
  have s2 : bk - a' - (bk - a) = a - a' := by ring
  have s3 : b0 - a' - (b0 - a) = a - a' := by ring
  rw [s1] at hc1 e1
  rw [s2] at hc2 e2
  rw [s3] at hc3 e3
  have hc1' := abs_le.mp hc1
  have hc2' := abs_le.mp hc2
  have hc3' := abs_le.mp hc3
  -- derivative errors
  have d1 : dist (deriv h c1) (deriv h (bi - a)) < M / 8 := by
    apply H1; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have d2 : dist (deriv h c2) (deriv h (bk - a)) < M / 8 := by
    apply H2; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have d3 : dist (deriv h c3) (deriv h (b0 - a)) < M / 8 := by
    apply H3; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  rw [Real.dist_eq] at d1 d2 d3
  obtain ⟨lam, hlamd⟩ : ∃ lam, lam = (β - b0) / (bk - b0) := ⟨_, rfl⟩
  obtain ⟨lami, hlamid⟩ : ∃ lami, lami = (bi - b0) / (bk - b0) := ⟨_, rfl⟩
  rw [← hlamd]
  rw [← hlamid] at hDd
  have hl0 : 0 < lam := by rw [hlamd]; apply div_pos <;> linarith
  have hl1 : lam < 1 := by rw [hlamd, div_lt_one hbk]; linarith
  have hll : (lam - lami) * (bk - b0) = β - bi := by
    rw [hlamd, hlamid, sub_mul, div_mul_cancel₀ _ hbk.ne', div_mul_cancel₀ _ hbk.ne']; ring
  have hβ4' : |β - bi| * (8 * (|K| + 1)) < (bk - b0) * M := by
    rw [← lt_div_iff₀ hK1, abs_sub_comm]; exact hβ4
  have hw : |(lam - lami) * K| < M / 8 := by
    rw [abs_mul]
    have h1 : |lam - lami| * (bk - b0) = |β - bi| := by
      rw [← hll, abs_mul, abs_of_pos hbk]
    have h2 : |lam - lami| * (8 * (|K| + 1)) < M := by
      have := hβ4'
      rw [← h1] at this
      exact aux2 _ _ _ _ hbk this
    exact aux1 _ _ _ (abs_nonneg _) (abs_nonneg _) h2
  obtain ⟨E, hEd⟩ : ∃ E, E = deriv h c1 - lam * deriv h c2 - (1 - lam) * deriv h c3 := ⟨_, rfl⟩
  have hED : E - D = (deriv h c1 - deriv h (bi - a)) - lam * (deriv h c2 - deriv h (bk - a)) -
      (1 - lam) * (deriv h c3 - deriv h (b0 - a)) - (lam - lami) * K := by
    rw [hEd, hDd, hKd]; ring
  have hEDb : |E - D| < M / 2 := by
    rw [hED, show M / 2 = 4 * (M / 8) by ring]
    exact aux3 _ _ _ _ _ _ hl0 hl1 d1 d2 d3 hw
  have hEpos : 0 < E * D := aux4 E D hD (by rw [← hMd]; exact hEDb)
  have hexpr : (h (β - a) + lam * h (bk - a') + (1 - lam) * h (b0 - a') -
      (h (β - a') + lam * h (bk - a) + (1 - lam) * h (b0 - a))) * (D * (a' - a)) =
      (a' - a) ^ 2 * (E * D) := by
    rw [hEd]
    linear_combination (D * (a' - a)) * (-e1 + lam * e2 + (1 - lam) * e3)
  rw [hexpr]
  have hu : a' - a ≠ 0 := by
    intro hu; rw [show a = a' by linarith, sub_self, abs_zero] at ha0; exact lt_irrefl _ ha0
  exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hu))) hEpos
