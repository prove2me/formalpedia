-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m20
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:04:27.98145+00:00
-- url     : https://prove2.me/submissions/bfa6a7ff-d517-4103-8a54-f24167fb8261

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open Set

theorem solution (I : ℝ → ℝ) (theta rate t u : ℝ) (htheta : 0 < theta)
    (hrate : 0 ≤ rate) (hu : 0 ≤ u) (hI : ContinuousOn I (Icc t (t+u)))
    (hphysical : ∀ v ∈ Icc t (t+u), 0 ≤ I v)
    (hode : ∀ v ∈ Ioo t (t+u), HasDerivAt I (-rate-theta*I v) v) :
    I (t+u) = Real.exp (-theta*u)*(I t+rate/theta)-rate/theta := by
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    simp
  · set g : ℝ → ℝ := fun v => Real.exp (theta * (v - t)) * (I v + rate / theta) with hg
    have hgc : ContinuousOn g (Icc t (t+u)) := by
      have h1 : Continuous (fun v : ℝ => Real.exp (theta * (v - t))) := by fun_prop
      exact h1.continuousOn.mul (hI.add continuousOn_const)
    have hgd : ∀ v ∈ Ioo t (t+u), HasDerivAt g ((fun _ => (0:ℝ)) v) v := by
      intro v hv
      have hc : theta * (rate / theta) = rate := mul_div_cancel₀ rate htheta.ne'
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (theta * (x - t)))
          (Real.exp (theta * (v - t)) * (theta * 1)) v :=
        (((hasDerivAt_id' v).sub_const t).const_mul theta).exp
      have h2 := h1.mul ((hode v hv).add_const (rate / theta))
      refine h2.congr_deriv ?_
      linear_combination (Real.exp (theta * (v - t))) * hc
    obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0:ℝ)) (by linarith) hgc hgd
    rw [eq_div_iff (by linarith)] at hc'
    have heq : g (t+u) = g t := by linarith
    simp only [hg, add_sub_cancel_left, sub_self, mul_zero, Real.exp_zero, one_mul] at heq
    rw [← heq, ← mul_assoc, ← Real.exp_add]
    have : -theta * u + theta * u = 0 := by ring
    rw [this, Real.exp_zero]
    ring
