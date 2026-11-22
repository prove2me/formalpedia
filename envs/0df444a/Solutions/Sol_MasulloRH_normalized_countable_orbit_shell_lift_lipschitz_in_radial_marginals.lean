-- Prove2me | solution 1 for MasulloRH.normalized_countable_orbit_shell_lift_lipschitz_in_radial_marginals
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:15:49.436742+00:00
-- url     : https://prove2.me/submissions/db662da8-0c00-4597-9237-e69f8e6ddae9

import Mathlib

private theorem shell_bound {D : Type*} {f g : D → ℝ}
    (hg : Summable g) (hf : ∀ r, |f r| ≤ g r) :
    Summable f ∧ |∑' r, f r| ≤ ∑' r, g r := by
  have h : Summable f := hg.of_norm_bounded (by simpa only [Real.norm_eq_abs] using hf)
  refine ⟨h, ?_⟩
  simpa only [Real.norm_eq_abs] using
    (norm_tsum_le_tsum_norm h.norm).trans
      (h.norm.tsum_le_tsum (by simpa only [Real.norm_eq_abs] using hf) hg)

theorem solution {D : Type*} [Group D] (b c : D → ℝ)
    (hb0 : ∀ r, 0 ≤ b r) (hc0 : ∀ r, 0 ≤ c r) (hb : HasSum b 1) (hc : HasSum c 1)
    (a : D → ℝ) (ha : ∀ ξ, |a ξ| ≤ 1) :
    |(∑' r, b r * ∑' s, b s * a (r⁻¹*s)) -
      (∑' r, c r * ∑' s, c s * a (r⁻¹*s))| ≤ 2 * ∑' r, |b r - c r| := by
  let m := fun (p : D → ℝ) (r : D) => ∑' s, p s * a (r⁻¹*s)
  let δ := ∑' r, |b r - c r|
  have hd : Summable (fun r => |b r - c r|) := by
    simpa only [Real.norm_eq_abs] using (hb.summable.sub hc.summable).norm
  have inner (p : D → ℝ) (h0 : ∀ r, 0 ≤ p r) (hp : HasSum p 1) (r : D) :
      Summable (fun s => p s * a (r⁻¹*s)) ∧ |m p r| ≤ 1 := by
    have e := shell_bound (f := fun s => p s * a (r⁻¹*s)) hp.summable (fun s => by
      rw [abs_mul,abs_of_nonneg (h0 s)]
      exact mul_le_of_le_one_right (h0 s) (ha _))
    simpa only [m,hp.tsum_eq] using e
  have outer (p : D → ℝ) (h0 : ∀ r, 0 ≤ p r) (hp : HasSum p 1) :
      Summable (fun r => p r * m p r) := by
    apply (shell_bound hp.summable _).1
    intro r
    rw [abs_mul,abs_of_nonneg (h0 r)]
    exact mul_le_of_le_one_right (h0 r) (inner p h0 hp r).2
  have diff (r : D) : |m b r - m c r| ≤ δ := by
    dsimp only [m, δ]
    rw [← (inner b hb0 hb r).1.tsum_sub (inner c hc0 hc r).1]
    apply (shell_bound hd _).2
    intro s
    rw [← sub_mul, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (ha _)
  have hg := hd.add (hc.summable.mul_right δ)
  change |(∑' r, b r * m b r) - (∑' r, c r * m c r)| ≤ 2 * δ
  rw [← (outer b hb0 hb).tsum_sub (outer c hc0 hc)]
  calc
    _ ≤ ∑' r, (|b r - c r| + c r * δ) := by
      apply (shell_bound hg _).2
      intro r
      rw [show b r * m b r - c r * m c r =
        (b r - c r) * m b r + c r * (m b r - m c r) by ring]
      apply (abs_add_le ..).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (hc0 r)]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (inner b hb0 hb r).2)
        (mul_le_mul_of_nonneg_left (diff r) (hc0 r))
    _ = 2 * δ := by
      rw [hd.tsum_add (hc.summable.mul_right δ),tsum_mul_right,hc.tsum_eq,one_mul]
      change δ + δ = 2 * δ
      ring
