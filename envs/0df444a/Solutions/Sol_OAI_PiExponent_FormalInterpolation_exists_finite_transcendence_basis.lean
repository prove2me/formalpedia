-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_finite_transcendence_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:32:12.64587+00:00
-- url     : https://prove2.me/submissions/4d2f902f-e2d7-4230-9862-7eefb31421d7

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem solution {K : Type*} [Field K] [Algebra Complex K] (hfin : Algebra.trdeg Complex K < Cardinal.aleph0) : ∃ (n : ℕ) (x : Fin n → K), IsTranscendenceBasis Complex x ∧ (Algebra.trdeg Complex K).toNat = n := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Complex K
  have hc := hs.cardinalMk_eq_trdeg
  have hfs : s.Finite := by
    rw [← Set.finite_coe_iff, ← Cardinal.lt_aleph0_iff_finite, hc]; exact hfin
  have : Fintype s := hfs.fintype
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : K), ?_, ?_⟩
  · exact hs.comp_equiv e.symm
  · rw [← hc]; simp
