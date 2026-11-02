-- Prove2me | solution 1 for GeomScoring.Characterization.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:21:46.736946+00:00
-- url     : https://prove2.me/submissions/f84d0967-d619-4ceb-847d-d2ef32c8dbb3

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model
import Theorems.Thm_GeomScoring_Characterization_proposition_4_losers
import Theorems.Thm_GeomScoring_Characterization_proposition_4_winners
import Theorems.Thm_GeomScoring_Characterization_first_last_equiv
import Theorems.Thm_GeomScoring_Characterization_geometric_recurrence

open GeomScoring.Characterization

namespace GSThm6

lemma aff_symm {k : ℕ} {u v : Fin k → ℝ} (h : AffEquiv u v) : AffEquiv v u := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨1 / a, -b / a, by positivity, fun j => ?_⟩
  rw [h j]; field_simp; ring

lemma aff_trans {k : ℕ} {u v w : Fin k → ℝ} (h1 : AffEquiv u v) (h2 : AffEquiv v w) :
    AffEquiv u w := by
  obtain ⟨a, b, ha, h1⟩ := h1
  obtain ⟨c, d, hc, h2⟩ := h2
  exact ⟨a * c, a * d + b, mul_pos ha hc, fun j => by rw [h1 j, h2 j]; ring⟩

lemma initSeg_aff {N : ℕ} {u v : Fin N → ℝ} (h : AffEquiv u v) (K : ℕ) (hK : K ≤ N) :
    AffEquiv (initSeg u K) (initSeg v K) := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨a, b, ha, fun j => ?_⟩
  simp only [initSeg]
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact h _

lemma finalSeg_aff {N : ℕ} {u v : Fin N → ℝ} (h : AffEquiv u v) (K : ℕ) (hK : K ≤ N) :
    AffEquiv (finalSeg u K) (finalSeg v K) := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨a, b, ha, fun j => ?_⟩
  simp only [finalSeg]
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact h _

lemma geom_strictAnti (p : ℝ) (hp : 0 < p) (m : ℕ) : StrictAnti (geomScore p m) := by
  intro i j hij
  rw [Fin.lt_def] at hij
  have hj := j.2
  have hlt : m - 1 - j.1 < m - 1 - i.1 := by omega
  simp only [geomScore]
  split_ifs with h1 h2
  · exact pow_lt_pow_right₀ h1 hlt
  · exact_mod_cast hlt
  · have : p < 1 := lt_of_le_of_ne (not_lt.mp h1) h2
    have := pow_lt_pow_right_of_lt_one₀ hp this hlt
    linarith

lemma geom_init (p : ℝ) (hp : 0 < p) (k m : ℕ) (hkm : k ≤ m) :
    AffEquiv (geomScore p k) (initSeg (geomScore p m) k) := by
  apply aff_symm
  by_cases h1 : 1 < p
  · refine ⟨p ^ (m - k), 0, by positivity, fun j => ?_⟩
    have := j.2
    simp only [initSeg, geomScore, if_pos h1]
    rw [dif_pos (by omega), ← pow_add]
    simp only [add_zero]
    congr 1; omega
  by_cases h2 : p = 1
  · refine ⟨1, ((m - k : ℕ) : ℝ), one_pos, fun j => ?_⟩
    have := j.2
    simp only [initSeg, geomScore, if_neg h1, if_pos h2]
    rw [dif_pos (by omega)]
    rw [show m - 1 - j.1 = (k - 1 - j.1) + (m - k) by omega]
    push_cast; ring
  · refine ⟨p ^ (m - k), 1 - p ^ (m - k), by positivity, fun j => ?_⟩
    have := j.2
    simp only [initSeg, geomScore, if_neg h1, if_neg h2]
    rw [dif_pos (by omega)]
    rw [show m - 1 - j.1 = (k - 1 - j.1) + (m - k) by omega, pow_add]
    ring

lemma geom_final (p : ℝ) (k m : ℕ) (hkm : k ≤ m) :
    AffEquiv (geomScore p k) (finalSeg (geomScore p m) k) := by
  refine ⟨1, 0, one_pos, fun j => ?_⟩
  have := j.2
  simp only [finalSeg]
  rw [dif_pos (by omega)]
  simp only [geomScore]
  rw [show m - 1 - (j.1 + (m - k)) = k - 1 - j.1 by omega]
  ring

lemma geom3_rel (p : ℝ) :
    geomScore p 3 0 - geomScore p 3 1 = p * (geomScore p 3 1 - geomScore p 3 2) := by
  simp only [geomScore]
  norm_num
  split_ifs with h1 h2
  · ring
  · subst h2; norm_num
  · ring

lemma geom3_unique (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : AffEquiv (geomScore p 3) (geomScore q 3)) : p = q := by
  obtain ⟨a, b, ha, h⟩ := h
  have D : 0 < geomScore q 3 1 - geomScore q 3 2 := by
    have := geom_strictAnti q hq 3 (show (1 : Fin 3) < 2 by decide); linarith
  have e := geom3_rel p
  have f := geom3_rel q
  rw [h 0, h 1, h 2] at e
  have : a * (q * (geomScore q 3 1 - geomScore q 3 2)) = a * (p * (geomScore q 3 1 - geomScore q 3 2)) := by
    rw [← f]; linarith
  have := mul_left_cancel₀ ha.ne' this
  exact (mul_right_cancel₀ D.ne' this).symm

lemma small (m : ℕ) (hm : m ≤ 2) (u w : Fin m → ℝ) (hu : StrictAnti u) (hw : StrictAnti w) :
    AffEquiv u w := by
  interval_cases m
  · exact ⟨1, 0, one_pos, fun j => j.elim0⟩
  · exact ⟨1, u 0 - w 0, one_pos, fun j => by fin_cases j; simp⟩
  · have h1 := hu (show (0 : Fin 2) < 1 by decide)
    have h2 := hw (show (0 : Fin 2) < 1 by decide)
    refine ⟨(u 0 - u 1) / (w 0 - w 1), u 1 - (u 0 - u 1) / (w 0 - w 1) * w 1,
      div_pos (by linarith) (by linarith), fun j => ?_⟩
    have hne : w 0 - w 1 ≠ 0 := by linarith
    fin_cases j
    · simp; field_simp; ring
    · simp

end GSThm6

open GSThm6 in
theorem solution (M : ℕ∞) (s : ScoringRule) :
    (IndepUnanimousWinners M s ∧ IndepUnanimousLosers M s) ↔
      ∃ p : ℝ, 0 < p ∧ ∀ m : ℕ, (m : ℕ∞) ≤ M → AffEquiv (s m) (geomScore p m) := by
  constructor
  · rintro ⟨hW, hL⟩
    have hL' := (proposition_4_losers M s).1 hL
    have hFL := first_last_equiv M s hW hL
    have hgeo : ∀ m : ℕ, (m : ℕ∞) ≤ M → 1 ≤ m →
        ∃ q : ℝ, 0 < q ∧ AffEquiv (s m) (geomScore q m) := fun m hm h1 =>
      geometric_recurrence m (s m) (hL'.1 m hm) (hFL (m - 1) m (by omega) hm)
    by_cases h3 : ((3 : ℕ) : ℕ∞) ≤ M
    · obtain ⟨p, hp, hp3⟩ := hgeo 3 h3 (by norm_num)
      refine ⟨p, hp, fun m hm => ?_⟩
      by_cases hm2 : m ≤ 2
      · exact small m hm2 _ _ (hL'.1 m hm) (geom_strictAnti p hp m)
      · by_cases hm3 : m = 3
        · subst hm3; exact hp3
        obtain ⟨q, hq, hmq⟩ := hgeo m hm (by omega)
        have hpq : p = q := by
          have e1 : AffEquiv (s 3) (initSeg (s m) 3) := hL'.2 3 m (by omega) hm
          have e2 := initSeg_aff hmq 3 (by omega)
          have e3 := aff_symm (geom_init q hq 3 m (by omega))
          exact geom3_unique p q hp hq (aff_trans (aff_symm hp3) (aff_trans e1 (aff_trans e2 e3)))
        rw [hpq]; exact hmq
    · refine ⟨1, one_pos, fun m hm => ?_⟩
      have hm2 : m ≤ 2 := by
        by_contra hc
        exact h3 (le_trans (by exact_mod_cast (by omega)) hm)
      exact small m hm2 _ _ (hL'.1 m hm) (geom_strictAnti 1 one_pos m)
  · rintro ⟨p, hp, hg⟩
    have hS : ∀ m : ℕ, (m : ℕ∞) ≤ M → StrictAnti (s m) := by
      intro m hm i j hij
      obtain ⟨a, b, ha, h⟩ := hg m hm
      rw [h i, h j]
      have := geom_strictAnti p hp m hij
      nlinarith
    have hk : ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → (k : ℕ∞) ≤ M := fun k m hkm hm =>
      le_trans (by exact_mod_cast hkm.le) hm
    refine ⟨(proposition_4_winners M s).2 ⟨hS, fun k m hkm hm => ?_⟩,
      (proposition_4_losers M s).2 ⟨hS, fun k m hkm hm => ?_⟩⟩
    · exact aff_trans (hg k (hk k m hkm hm)) (aff_trans (geom_final p k m hkm.le)
        (finalSeg_aff (aff_symm (hg m hm)) k hkm.le))
    · exact aff_trans (hg k (hk k m hkm hm)) (aff_trans (geom_init p hp k m hkm.le)
        (initSeg_aff (aff_symm (hg m hm)) k hkm.le))
