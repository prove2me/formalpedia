-- Prove2me | solution 1 for MatchCongestion.Welfare.theorem_2_root_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:28:02.208003+00:00
-- url     : https://prove2.me/submissions/28d3b2fd-04ba-4e18-8e30-edb030045220

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

noncomputable def mcf (A r s : ℝ) : ℝ := 1 - Real.exp (-(A * s * (1 - s))) - r * s

theorem mcf_concave (A r : ℝ) (hA : 0 ≤ A) : ConcaveOn ℝ Set.univ (mcf A r) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul, mcf]
  have hq : A * (a * x + (1 - a) * y) ^ 2 - A * (a * x + (1 - a) * y) ≤
      a * (A * x ^ 2 - A * x) + (1 - a) * (A * y ^ 2 - A * y) := by
    have : a * (A * x ^ 2 - A * x) + (1 - a) * (A * y ^ 2 - A * y)
        - (A * (a * x + (1 - a) * y) ^ 2 - A * (a * x + (1 - a) * y))
        = A * (a * (1 - a) * (x - y) ^ 2) := by ring
    have h2 : 0 ≤ A * (a * (1 - a) * (x - y) ^ 2) := by
      apply mul_nonneg hA; apply mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    linarith
  have h1 := Real.exp_le_exp.mpr hq
  have h2 := convexOn_exp.2 (Set.mem_univ (A * x ^ 2 - A * x)) (Set.mem_univ (A * y ^ 2 - A * y))
    ha hb (by ring : a + (1 - a) = 1)
  simp only [smul_eq_mul] at h2
  have e : ∀ s : ℝ, -(A * s * (1 - s)) = A * s ^ 2 - A * s := fun s => by ring
  simp only [e]
  nlinarith

theorem mcf_pos_small (A r : ℝ) (hr : 0 < r) (hrA : r < A) (s : ℝ) (hs : 0 < s)
    (hσ : s < (A - r) / (A * (1 + r))) : 0 < mcf A r s := by
  have hA : 0 < A := hr.trans hrA
  have hAr : 0 < A * (1 + r) := by positivity
  have hs1 : s * (A * (1 + r)) < A - r := by rwa [lt_div_iff₀ hAr] at hσ
  have hs2 : s < 1 := by nlinarith
  set u := A * s * (1 - s) with hu
  have hu0 : 0 < u := by rw [hu]; apply mul_pos (mul_pos hA hs); linarith
  have key : r * s * (1 + u) < u := by
    have : r * (1 + u) < A * (1 - s) := by
      have : u ≤ A * s := by rw [hu]; nlinarith
      nlinarith
    have h3 : r * s * (1 + u) < s * (A * (1 - s)) := by nlinarith
    rw [hu]; nlinarith
  have e1 : Real.exp (-u) * (1 + u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    have h4 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h5 := Real.exp_pos (-u)
    nlinarith
  unfold mcf
  rw [← hu]
  by_contra hcon
  push_neg at hcon
  have h6 : 1 - r * s ≤ Real.exp (-u) := by linarith
  nlinarith

theorem mcf_chord (A r : ℝ) (hA : 0 ≤ A) (s' s s'' : ℝ) (h1 : s' < s) (h2 : s < s'') :
    ((s'' - s) / (s'' - s')) * mcf A r s' + ((s - s') / (s'' - s')) * mcf A r s'' ≤ mcf A r s := by
  have hd : 0 < s'' - s' := by linarith
  have ha : 0 ≤ (s'' - s) / (s'' - s') := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (s - s') / (s'' - s') := div_nonneg (by linarith) hd.le
  have hab : (s'' - s) / (s'' - s') + (s - s') / (s'' - s') = 1 := by
    field_simp; ring
  have := (mcf_concave A r hA).2 (Set.mem_univ s') (Set.mem_univ s'') ha hb hab
  simp only [smul_eq_mul] at this
  have e : (s'' - s) / (s'' - s') * s' + (s - s') / (s'' - s') * s'' = s := by
    field_simp; ring
  rwa [e] at this

/-- sign pattern around a positive root -/
theorem mcf_sign (A r : ℝ) (hr : 0 < r) (hrA : r < A) (st : ℝ) (hst : 0 < st)
    (hroot : mcf A r st = 0) :
    (∀ s, 0 < s → s < st → 0 < mcf A r s) ∧ (∀ s, st < s → mcf A r s < 0) := by
  have hA : 0 < A := hr.trans hrA
  have hσpos : 0 < (A - r) / (A * (1 + r)) := by
    apply div_pos (by linarith); positivity
  set σ := (A - r) / (A * (1 + r)) with hσ
  constructor
  · intro s hs hsst
    set s' := min s σ / 2 with hs'
    have hm : 0 < min s σ := lt_min hs hσpos
    have hs'0 : 0 < s' := by rw [hs']; linarith
    have hs's : s' < s := by rw [hs']; have := min_le_left s σ; linarith
    have hs'σ : s' < σ := by rw [hs']; have := min_le_right s σ; linarith
    have hp := mcf_pos_small A r hr hrA s' hs'0 hs'σ
    have hc := mcf_chord A r hA.le s' s st hs's hsst
    rw [hroot] at hc
    have : 0 < (st - s) / (st - s') := div_pos (by linarith) (by linarith)
    nlinarith [mul_pos this hp]
  · intro s hs
    set s' := min st σ / 2 with hs'
    have hm : 0 < min st σ := lt_min hst hσpos
    have hs'0 : 0 < s' := by rw [hs']; linarith
    have hs's : s' < st := by rw [hs']; have := min_le_left st σ; linarith
    have hs'σ : s' < σ := by rw [hs']; have := min_le_right st σ; linarith
    have hp := mcf_pos_small A r hr hrA s' hs'0 hs'σ
    have hc := mcf_chord A r hA.le s' st s hs's hs
    rw [hroot] at hc
    have h1 : 0 < (s - st) / (s - s') := div_pos (by linarith) (by linarith)
    have h2 : 0 < (st - s') / (s - s') := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos h1 hp, mul_nonneg h2.le hcon]

theorem mcf_exists (A r : ℝ) (hr : 0 < r) (hrA : r < A) :
    ∃ s, 0 < s ∧ s < 1 ∧ mcf A r s = 0 := by
  have hA : 0 < A := hr.trans hrA
  have hσpos : 0 < (A - r) / (A * (1 + r)) := by
    apply div_pos (by linarith); positivity
  set σ := (A - r) / (A * (1 + r)) with hσ
  have hσ1 : σ < 1 := by
    rw [hσ, div_lt_one (by positivity)]; nlinarith
  have hp := mcf_pos_small A r hr hrA (σ / 2) (by linarith) (by linarith)
  have h1 : mcf A r 1 = -r := by simp [mcf]
  have hcont : ContinuousOn (mcf A r) (Set.Icc (σ / 2) 1) := by
    unfold mcf; fun_prop
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' (by linarith : σ / 2 ≤ 1) hcont
    (show (0 : ℝ) ∈ Set.Icc (mcf A r 1) (mcf A r (σ / 2)) from ⟨by rw [h1]; linarith, hp.le⟩)
  refine ⟨s, by linarith [hs.1], ?_, hz⟩
  rcases hs.2.lt_or_eq with h | h
  · exact h
  · exfalso; rw [h, h1] at hz; linarith

theorem mc_eq13_iff (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : 0 < p) :
    Eq13 P p ↔ mcf (P.r * P.β / P.ca) P.r (1 - P.ca / p) = 0 := by
  unfold Eq13 mcf
  have : -(P.r * P.β / p) * (1 - P.ca / p) =
      -(P.r * P.β / P.ca * (1 - P.ca / p) * (1 - (1 - P.ca / p))) := by
    field_simp; ring
  rw [this]
  constructor <;> intro h <;> linarith

theorem solution (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq13 P p := by
  obtain ⟨hmax, hr, hβ, _, hca, hcs⟩ := hP
  have hcaβ : P.ca < P.β := lt_of_le_of_lt (le_max_left _ _) hmax
  have hrA : P.r < P.r * P.β / P.ca := by
    rw [lt_div_iff₀ hca]; nlinarith
  obtain ⟨s, hs0, hs1, hsz⟩ := mcf_exists _ _ hr hrA
  have h1s : 0 < 1 - s := by linarith
  have hp : P.ca < P.ca / (1 - s) := by
    rw [lt_div_iff₀ h1s]; nlinarith
  have hcs' : 1 - P.ca / (P.ca / (1 - s)) = s := by field_simp; ring
  refine ⟨P.ca / (1 - s), ⟨hp, ?_⟩, ?_⟩
  · rw [mc_eq13_iff P hca _ (hca.trans hp), hcs']; exact hsz
  · rintro p ⟨hpc, hpe⟩
    have hp0 : 0 < p := hca.trans hpc
    have hz := (mc_eq13_iff P hca p hp0).mp hpe
    set s' := 1 - P.ca / p with hs'
    have hs'0 : 0 < s' := by
      rw [hs', sub_pos, div_lt_one hp0]; exact hpc
    have hs'1 : s' < 1 := by
      rw [hs']; have : 0 < P.ca / p := div_pos hca hp0
      linarith
    have : s' = s := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := (mcf_sign _ _ hr hrA s' hs'0 hz).2 s h
        linarith
      · have := (mcf_sign _ _ hr hrA s hs0 hsz).2 s' h
        linarith
    have e : P.ca / p = 1 - s := by rw [← this, hs']; ring
    rw [← e]; field_simp
