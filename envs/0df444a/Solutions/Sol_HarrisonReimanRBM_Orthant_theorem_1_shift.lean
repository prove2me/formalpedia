-- Prove2me | solution 1 for HarrisonReimanRBM.Orthant.theorem_1_shift
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:08:12.19293+00:00
-- url     : https://prove2.me/submissions/85ac3ccc-7466-454c-b184-7f713ceafdf1

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

open Reiman84.QueueLength

open HarrisonReimanRBM.Orthant Reiman84.QueueLength in
theorem solution {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (x y z : ℝ → Fin K → ℝ) (h : IsReflectionPair Q x y z)
    (T : ℝ) (hT : 0 < T) :
    IsReflectionPair Q (shiftX T x z) (shiftY T y) (shiftZ T z) := by
  obtain ⟨⟨hxc, _⟩, hyc, hzc, heq, hzpos, ⟨hymono, hy0⟩, hcomp⟩ := h
  have hmaps : Set.MapsTo (fun t : ℝ => T + t) (Set.Ici 0) (Set.Ici 0) := by
    intro t ht
    simp only [Set.mem_Ici] at ht ⊢
    linarith
  have hshift : ContinuousOn (fun t : ℝ => T + t) (Set.Ici 0) := by fun_prop
  have hxs : ContinuousOn (fun t => x (T + t)) (Set.Ici 0) := hxc.comp hshift hmaps
  have hys : ContinuousOn (fun t => y (T + t)) (Set.Ici 0) := hyc.comp hshift hmaps
  have hzs : ContinuousOn (fun t => z (T + t)) (Set.Ici 0) := hzc.comp hshift hmaps
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold shiftX
    exact (continuousOn_const.add hxs).sub continuousOn_const
  · unfold shiftX
    simp only [add_zero, add_sub_cancel_right]
    exact hzpos T hT.le
  · unfold shiftY
    exact hys.sub continuousOn_const
  · unfold shiftZ
    exact hzs
  · intro t ht
    unfold shiftX shiftY shiftZ
    rw [heq (T + t) (by linarith), heq T hT.le, Matrix.sub_vecMul]
    abel
  · intro t ht
    unfold shiftZ
    exact hzpos (T + t) (by linarith)
  · intro s hs t ht hst
    unfold shiftY
    simp only [Set.mem_Ici] at hs ht
    exact sub_le_sub_right (hymono (show T + s ∈ Set.Ici 0 by simp; linarith)
      (show T + t ∈ Set.Ici 0 by simp; linarith) (by linarith)) _
  · unfold shiftY
    simp
  · intro j s t hs hst hpos
    unfold shiftY
    simp only [Pi.sub_apply]
    have := hcomp j (T + s) (T + t) (by linarith) (by linarith) (by
      intro r hr
      have h1 := hpos (r - T) ⟨by linarith [hr.1], by linarith [hr.2]⟩
      unfold shiftZ at h1
      simpa using h1)
    rw [this]
