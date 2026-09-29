-- Prove2me | solution 1 for HarmonicOscillator.of_polarHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T02:24:48.608185+00:00
-- url     : https://prove2.me/submissions/299337d5-9df9-4775-946f-1717c10abae4

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha : ℝ) (g g' g'' : ℝ → E)
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (wr wrr wt wtt : ℝ → ℝ → E)
    (hwr : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s ^ alpha • g t) (wr r t) r)
    (hwrr : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => wr s t) (wrr r t) r)
    (hwt : ∀ r t : ℝ, HasDerivAt (fun u : ℝ => r ^ alpha • g u) (wt r t) t)
    (hwtt : ∀ r t : ℝ, HasDerivAt (fun u : ℝ => wt r u) (wtt r t) t)
    (hharm : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      wrr r t + r⁻¹ • wr r t + (r ^ 2)⁻¹ • wtt r t = 0) :
    ∀ t : ℝ, g'' t = -(alpha ^ 2) • g t := by
  -- the radial derivatives
  have hexp : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s ^ alpha • g t) ((alpha * r ^ (alpha - 1)) • g t) r := by
    intro r hr t
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hr))).smul_const (g t)
  have hwr_eq : ∀ r : ℝ, 0 < r → ∀ t : ℝ, wr r t = (alpha * r ^ (alpha - 1)) • g t :=
    fun r hr t => (hwr r hr t).unique (hexp r hr t)
  have hexp2 : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => wr s t)
        ((alpha * ((alpha - 1) * r ^ (alpha - 1 - 1))) • g t) r := by
    intro r hr t
    have hbase : HasDerivAt (fun s : ℝ => (alpha * s ^ (alpha - 1)) • g t)
        ((alpha * ((alpha - 1) * r ^ (alpha - 1 - 1))) • g t) r :=
      (((Real.hasDerivAt_rpow_const
        (p := alpha - 1) (Or.inl (ne_of_gt hr))).const_mul alpha).smul_const (g t))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds (show r ∈ Set.Ioi (0:ℝ) from hr)] with s hs
    exact hwr_eq s hs t
  have hwrr_eq : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      wrr r t = (alpha * ((alpha - 1) * r ^ (alpha - 1 - 1))) • g t :=
    fun r hr t => (hwrr r hr t).unique (hexp2 r hr t)
  -- the angular derivatives
  have hwt_eq : ∀ r t : ℝ, wt r t = r ^ alpha • g' t :=
    fun r t => (hwt r t).unique ((hg t).const_smul (r ^ alpha))
  have hwtt_eq : ∀ r t : ℝ, wtt r t = r ^ alpha • g'' t := by
    intro r t
    refine (hwtt r t).unique ?_
    have hfun : (fun u : ℝ => wt r u) = fun u : ℝ => r ^ alpha • g' u := by
      funext u; exact hwt_eq r u
    rw [hfun]
    exact (hg' t).const_smul (r ^ alpha)
  -- evaluate the equation at r = 1
  intro t
  have h1 := hharm 1 one_pos t
  rw [hwr_eq 1 one_pos t, hwrr_eq 1 one_pos t, hwtt_eq 1 t] at h1
  simp only [Real.one_rpow, inv_one, one_smul, one_pow, mul_one] at h1
  linear_combination (norm := module) h1
