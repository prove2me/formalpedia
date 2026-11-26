-- Prove2me | solution 1 for Kyprianou.Ch04.itoRemainderClampedContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:21:56.202806+00:00
-- url     : https://prove2.me/submissions/751421c5-41d2-484f-a9e1-a721db5df4d1

import Mathlib
open Set
set_option autoImplicit false

/-- The time-clamped Taylor remainder is continuous in its time, state and mark. -/
theorem solution (f g : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ)) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      f (max 0 p.1) (p.2.1+p.2.2) - f (max 0 p.1) p.2.1 -
        p.2.2*g (max 0 p.1) p.2.1) := by
  have hc : Continuous (fun p : ℝ × ℝ × ℝ => max 0 p.1) :=
    continuous_const.max continuous_fst
  have hx : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) := continuous_snd.comp continuous_snd
  have h1 : Continuous (fun p : ℝ × ℝ × ℝ => f (max 0 p.1) (p.2.1+p.2.2)) :=
    hf.comp_continuous (hc.prodMk (hx.add hz)) (fun p => ⟨by simp,mem_univ _⟩)
  have h2 : Continuous (fun p : ℝ × ℝ × ℝ => f (max 0 p.1) p.2.1) :=
    hf.comp_continuous (hc.prodMk hx) (fun p => ⟨by simp,mem_univ _⟩)
  have h3 : Continuous (fun p : ℝ × ℝ × ℝ => g (max 0 p.1) p.2.1) :=
    hg.comp_continuous (hc.prodMk hx) (fun p => ⟨by simp,mem_univ _⟩)
  exact (h1.sub h2).sub (hz.mul h3)
