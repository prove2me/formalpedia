-- Prove2me | solution 1 for MassartDKW.Binom.lemma_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:14:36.173726+00:00
-- url     : https://prove2.me/submissions/cc5f06ce-6bbb-4812-b2d5-22e4b76dcce8

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting



namespace MassartDKW.Binom

/-- `g u = log(1+u) - 3u(6+u)/(2(3+u)^2)`, with `g' u = 1/(1+u) - 27/(3+u)^3 ≥ 0`. -/
noncomputable def gB (u : ℝ) : ℝ := Real.log (1 + u) - 3 * u * (6 + u) / (2 * (3 + u) ^ 2)

/-- `f u = (1+u) log(1+u) - u - u^2/(2(1+u/3))`, with `f' = g`. -/
noncomputable def fB (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u - u ^ 2 / (2 * (1 + u / 3))

lemma log_one_add_hasDerivAt {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have := ((hasDerivAt_id u).const_add 1).log h1
  simp only [id] at this
  exact this.congr_deriv (by ring)

lemma gB_hasDerivAt {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt gB (1 / (1 + u) - 27 / (3 + u) ^ 3) u := by
  have h3 : (3 + u : ℝ) ≠ 0 := by positivity
  have h3' : (2 * (3 + u) ^ 2 : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun u : ℝ => 3 * u * (6 + u)) (3 * 1 * (6 + u) + 3 * u * 1) u := by
    have := ((hasDerivAt_id u).const_mul (3:ℝ)).mul ((hasDerivAt_id u).const_add 6)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hb : HasDerivAt (fun u : ℝ => 2 * (3 + u) ^ 2) (2 * (2 * (3 + u))) u := by
    have := (((hasDerivAt_id u).const_add 3).pow 2).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := (log_one_add_hasDerivAt hu).sub (ha.div hb h3')
  refine hd.congr_deriv ?_
  field_simp
  ring

lemma fB_hasDerivAt {u : ℝ} (hu : 0 ≤ u) : HasDerivAt fB (gB u) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have h3 : (3 + u : ℝ) ≠ 0 := by positivity
  have h2 : (2 * (1 + u / 3) : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u))
      (1 * Real.log (1 + u) + (1 + u) * (1 / (1 + u))) u := by
    have := ((hasDerivAt_id u).const_add 1).mul (log_one_add_hasDerivAt hu)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hb : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hc : HasDerivAt (fun u : ℝ => 2 * (1 + u / 3)) (2 * (1 / 3)) u := by
    have := (((hasDerivAt_id u).div_const 3).const_add 1).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := (ha.sub (hasDerivAt_id u)).sub (hb.div hc h2)
  refine hd.congr_deriv ?_
  unfold gB
  field_simp
  ring

lemma gB_zero : gB 0 = 0 := by simp [gB]
lemma fB_zero : fB 0 = 0 := by simp [fB]

lemma gB_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gB u := by
  have hmono : MonotoneOn gB (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact (gB_hasDerivAt hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (gB_hasDerivAt (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(gB_hasDerivAt (le_of_lt hx')).deriv]
      have h27 : 27 * (1 + x) ≤ (3 + x) ^ 3 := by nlinarith [sq_nonneg x, pow_pos hx' 3]
      have hpos : (0:ℝ) < (3 + x) ^ 3 := by positivity
      have : 27 / (3 + x) ^ 3 ≤ 1 / (1 + x) := by
        rw [div_le_div_iff₀ hpos (by positivity)]
        linarith
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  rwa [gB_zero] at this

lemma fB_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ fB u := by
  have hmono : MonotoneOn fB (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact (fB_hasDerivAt hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (fB_hasDerivAt (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(fB_hasDerivAt (le_of_lt hx')).deriv]
      exact gB_nonneg (le_of_lt hx')
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  rwa [fB_zero] at this

/-- Bennett-type inequality: `(1+u) log(1+u) - u ≥ u^2/(2(1+u/3))` for `u ≥ 0`. -/
lemma bennett_ineq {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 * (1 + u / 3)) ≤ (1 + u) * Real.log (1 + u) - u := by
  have := fB_nonneg hu
  unfold fB at this
  linarith

/-- Scaled version: `ε + ε²/(2(p+ε/3)) ≤ (p+ε) log((p+ε)/p)`. -/
lemma key_ineq {p ε : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) :
    ε + ε ^ 2 / (2 * (p + ε / 3)) ≤ (p + ε) * Real.log ((p + ε) / p) := by
  have hu : 0 ≤ ε / p := by positivity
  have h := bennett_ineq hu
  have e1 : (p + ε) / p = 1 + ε / p := by field_simp
  rw [e1]
  have e2 : (p + ε) * Real.log (1 + ε / p) = p * ((1 + ε / p) * Real.log (1 + ε / p)) := by
    field_simp
  have e3 : ε + ε ^ 2 / (2 * (p + ε / 3)) = p * ((ε / p) ^ 2 / (2 * (1 + ε / p / 3)) + ε / p) := by
    field_simp
    ring
  rw [e2, e3]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hp)
  linarith

theorem lemma_1_ii_core (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hεq : ε ≤ 1 - p) :
    (ε < 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3))
          + ε * phi (ε / (1 - p - ε)) / (ε / (1 - p - ε)) ≤ h p ε) ∧
    (ε = 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + ε / 4 ≤ h p ε) := by
  have hK := key_ineq hp (le_of_lt hε)
  constructor
  · intro hlt
    have hq : 0 < 1 - p - ε := by linarith
    have hq' : 0 < 1 - p := by linarith
    set t := ε / (1 - p - ε) with ht
    have htpos : 0 < t := by positivity
    have e1 : 1 + t = (1 - p) / (1 - p - ε) := by rw [ht]; field_simp; ring
    have e2 : Real.log (1 + t) = - Real.log ((1 - p - ε) / (1 - p)) := by
      rw [e1, ← Real.log_inv, inv_div]
    have e3 : ε * phi t / t
        = ε - ε ^ 2 / (2 * (1 - p - ε / 3)) + (1 - p - ε) * Real.log ((1 - p - ε) / (1 - p)) := by
      unfold phi
      rw [e2, ht]
      have hQ : (1 - p - ε) ≠ 0 := hq.ne'
      have e13 : (1 - p - ε / 3) = (1 - p - ε) + 2 * ε / 3 := by ring
      rw [e13]
      generalize hL : Real.log ((1 - p - ε) / (1 - p)) = L
      generalize hQe : 1 - p - ε = Q at hQ hq ⊢
      have h5 : Q + 2 * ε / 3 ≠ 0 := by positivity
      have h6 : 3 * Q + 2 * ε ≠ 0 := by positivity
      have h7 : 1 + 2 * (ε / Q) / 3 ≠ 0 := by positivity
      field_simp
      ring
    have e4 : ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + (ε - ε ^ 2 / (2 * (1 - p - ε / 3)))
        = ε + ε ^ 2 / (2 * (p + ε / 3)) := by
      have h3' : (1 - p - ε / 3 : ℝ) ≠ 0 := by intro h; linarith
      have h4 : (p + ε / 3 : ℝ) ≠ 0 := by positivity
      generalize hD : 1 - p - ε / 3 = D at h3'
      generalize hA : p + ε / 3 = A at h4
      have hAD : A + D = 1 := by rw [← hA, ← hD]; ring
      field_simp
      linear_combination (-ε) * hAD
    unfold h
    rw [e3]
    linarith
  · intro heq
    subst heq
    unfold h
    have e0 : (1 - p - (1 - p)) = (0:ℝ) := by ring
    rw [e0, zero_mul, add_zero]
    have h3 : (0:ℝ) < 1 - p - (1 - p) / 3 := by linarith
    have h4 : (0:ℝ) < p + (1 - p) / 3 := by linarith
    have e5 : (1 - p) ^ 2 / (2 * (p + (1 - p) / 3) * (1 - p - (1 - p) / 3)) + (1 - p) / 4
        = (1 - p) + (1 - p) ^ 2 / (2 * (p + (1 - p) / 3)) := by
      field_simp
      ring
    rw [e5]
    exact hK

end MassartDKW.Binom

open MassartDKW.Binom


theorem solution (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hεq : ε ≤ 1 - p) :
    (ε < 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3))
          + ε * phi (ε / (1 - p - ε)) / (ε / (1 - p - ε)) ≤ h p ε) ∧
    (ε = 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + ε / 4 ≤ h p ε) := by
  exact lemma_1_ii_core p ε hp hε hεq
