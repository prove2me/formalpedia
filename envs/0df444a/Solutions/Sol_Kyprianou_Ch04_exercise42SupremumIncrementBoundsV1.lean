-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42SupremumIncrementBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:32:18.557798+00:00
-- url     : https://prove2.me/submissions/647692a3-0999-42d9-97e7-181d6c053e5a

import Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementBoundsV1
set_option autoImplicit false

theorem solution
    (X : NNReal → Real) (c : Real) (hc : 0 < c)
    (hzero : X 0 = 0)
    (hMon : Monotone (fun t : NNReal => (t : Real) * c - X t)) :
    let U : NNReal → Real := fun t => sSup (X '' Set.Iic t)
    U 0 = 0 ∧ (∀ t, 0 ≤ U t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ U t - U s ∧ U t - U s ≤ c * ((t : Real) - (s : Real))) ∧
    LipschitzWith c.toNNReal U := by
  intro U
  have hi (s t : NNReal) (h : s ≤ t) :
      X t - X s ≤ c * ((t : Real) - (s : Real)) := by
    have hh := hMon h
    dsimp only at hh
    linarith
  have hn (t : NNReal) : 0 ≤ U t := by
    have hb : BddAbove (X '' Set.Iic t) := by
      refine ⟨c * (t : Real), ?_⟩
      rintro y ⟨u, hu, rfl⟩
      have h := hi 0 u zero_le
      simp only [hzero, NNReal.coe_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left (show (u : Real) ≤ (t : Real) from hu) hc.le)
    have hmem : X 0 ∈ X '' Set.Iic t := ⟨0, (show 0 ≤ t from zero_le), rfl⟩
    simpa only [hzero] using le_csSup hb hmem
  have he : (fun t : NNReal => max 0 (sSup (X '' Set.Iic t))) = U :=
    funext (fun t => max_eq_right (hn t))
  have H := Kyprianou.Ch04.idleRegulatorIncrementBoundsV1 X c 0 hc le_rfl hzero hi
  have he' (t : NNReal) : max 0 (sSup (X '' Set.Iic t)) = U t :=
    congrFun he t
  have H' : U 0 = 0 ∧ (∀ t, X t ≤ U t) ∧
      (∀ s t : NNReal, s ≤ t →
        0 ≤ U t - U s ∧
        U t - U s ≤ max 0 (X s - U s + c * ((t : Real) - (s : Real)))) ∧
      LipschitzWith c.toNNReal U := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [he'] using H.1
    · intro t
      simpa only [he'] using H.2.1 t
    · intro s t h
      simpa only [he'] using H.2.2.1 s t h
    · exact he ▸ H.2.2.2
  clear H
  refine ⟨H'.1, hn, ?_, H'.2.2.2⟩
  intro s t hst
  have h := H'.2.2.1 s t hst
  have hx := H'.2.1 s
  have ht : 0 ≤ c * ((t : Real) - (s : Real)) :=
    mul_nonneg hc.le (sub_nonneg.mpr (show (s : Real) ≤ (t : Real) from hst))
  exact ⟨h.1, h.2.trans (max_le ht (by linarith))⟩
