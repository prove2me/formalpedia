-- Prove2me | solution 1 for GeomDRSub.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:52:05.684077+00:00
-- url     : https://prove2.me/submissions/6bfa0257-0e53-4324-ac3a-f440911d1924

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_diagPt
import Definitions.Def_GeomDRSub_pd
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular

open GeomDRSub in
theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : IsDRSubmodular f) :
    (∀ i : Fin d, ∀ y ∈ cube d, |pd f i y| ≤ max |pd f i 0| |pd f i (diagPt d 1)|) ∧
      ∀ B : ℝ, (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) →
        ∑ i : Fin d, (max |pd f i 0| |pd f i (diagPt d 1)|) ^ 2 ≤ 2 * B ^ 2 := by
  have hdiag : ∀ j, (diagPt d 1) j = 1 := fun j => by
    show (WithLp.toLp 2 (fun _ => (1 : ℝ)) : EuclideanSpace ℝ (Fin d)) j = 1
    rw [PiLp.toLp_apply]
  have hzero : ∀ j, (0 : EuclideanSpace ℝ (Fin d)) j = 0 := fun j => PiLp.zero_apply _ _
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ cube d := fun j => by
    rw [hzero]; exact ⟨le_refl 0, zero_le_one⟩
  have h1 : diagPt d 1 ∈ cube d := fun j => by
    rw [hdiag]; exact ⟨zero_le_one, le_refl 1⟩
  refine ⟨fun i y hy => ?_, fun B hB => ?_⟩
  · have hl := hf.2 y hy (diagPt d 1) h1 (fun j => by rw [hdiag]; exact (hy j).2) i
    have hu := hf.2 0 h0 y hy (fun j => by rw [hzero]; exact (hy j).1) i
    rw [max_comm]
    exact abs_le_max_abs_abs hl hu
  · have hn0 := hB 0 h0
    have hn1 := hB _ h1
    have hsq : ∀ y, ‖gradQ f y‖ ^ 2 = ∑ i, (pd f i y) ^ 2 := by
      intro y
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      simp [gradQ, Real.norm_eq_abs, sq_abs]
    have hm : ∀ a b : ℝ, (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      intro a b
      have ha := sq_abs a
      have hb := sq_abs b
      rcases le_total |a| |b| with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg a]
      · rw [max_eq_left h]; nlinarith [sq_nonneg b]
    calc ∑ i : Fin d, (max |pd f i 0| |pd f i (diagPt d 1)|) ^ 2
        ≤ ∑ i : Fin d, ((pd f i 0) ^ 2 + (pd f i (diagPt d 1)) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hm _ _)
      _ = ‖gradQ f 0‖ ^ 2 + ‖gradQ f (diagPt d 1)‖ ^ 2 := by
          rw [hsq, hsq, Finset.sum_add_distrib]
      _ ≤ B ^ 2 + B ^ 2 :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) hn0 2)
            (pow_le_pow_left₀ (norm_nonneg _) hn1 2)
      _ = 2 * B ^ 2 := by ring
