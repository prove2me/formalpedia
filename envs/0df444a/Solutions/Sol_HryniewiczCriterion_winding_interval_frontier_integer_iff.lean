-- Prove2me | solution 1 for HryniewiczCriterion.winding_interval_frontier_integer_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T20:11:20.375581+00:00
-- url     : https://prove2.me/submissions/e35cf3f3-ace1-4a5e-a5d6-6e5cc173ae26

import Theorems.Thm_HryniewiczCriterion_winding_endpoint_profile
import Theorems.Thm_HryniewiczCriterion_unipotent_rotation_profile_extremum
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped ContDiff
open HryniewiczCriterion

theorem solution (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    (∃ k : ℤ, sInf (windingInterval φ) = k ∨ sSup (windingInterval φ) = k) ↔
      (φ 1 - 1).det = 0 := by
  obtain ⟨Δ, hcont, himage, hrange, hpolar⟩ :=
    winding_endpoint_profile φ hφ hsymp h0
  have hcompact : IsCompact (windingInterval φ) := by
    rw [himage]
    exact isCompact_Icc.image hcont
  have hne : (windingInterval φ).Nonempty := by
    rw [hrange]
    exact Set.range_nonempty Δ
  have hsingular (s : ℝ) (k : ℤ) (hs : Δ s = k)
      (hz : ∀ r : ℝ, 0 < r →
        HasDerivAt Δ ((1 / r ^ 2 - 1) / (2 * Real.pi)) s →
        (1 / r ^ 2 - 1) / (2 * Real.pi) = 0) : (φ 1 - 1).det = 0 := by
    obtain ⟨r, hr, hvec, hderiv⟩ := hpolar s
    have hzero := hz r hr hderiv
    have hnum : 1 / r ^ 2 - 1 = 0 :=
      (div_eq_zero_iff).mp hzero |>.resolve_right (ne_of_gt (by positivity))
    have hr2 : r ^ 2 = 1 := by
      have hpow : r ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
      have hone : 1 / r ^ 2 = 1 := by linarith
      exact (div_eq_one_iff_eq hpow).mp hone |>.symm
    have hr1 : r = 1 := by nlinarith
    have hrot : rotationVector (s + 2 * Real.pi * (k : ℝ)) = rotationVector s := by
      rw [mul_comm (2 * Real.pi) (k : ℝ)]
      ext i
      fin_cases i <;>
        simp [rotationVector, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    rw [hs, hr1, hrot, one_smul] at hvec
    have hkernel : (φ 1 - 1).mulVec (rotationVector s) = 0 := by
      rw [Matrix.sub_mulVec, hvec, Matrix.one_mulVec, sub_self]
    by_contra hdet
    have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet hkernel
    have hc : Real.cos s = 0 := by
      simpa [rotationVector] using congrFun hv 0
    have hsin : Real.sin s = 0 := by
      simpa [rotationVector] using congrFun hv 1
    have hid := Real.sin_sq_add_cos_sq s
    rw [hc, hsin] at hid
    norm_num at hid
  constructor
  · rintro ⟨k, hk | hk⟩
    · have hmem := hcompact.sInf_mem hne
      rw [hk, hrange] at hmem
      obtain ⟨s, hs⟩ := hmem
      apply hsingular s k hs
      intro r hr hd
      have hmin : IsMinOn Δ Set.univ s := by
        intro t _
        rw [hs, ← hk]
        apply csInf_le hcompact.bddBelow
        rw [hrange]
        exact Set.mem_range_self t
      exact (hmin.isLocalMin (by simp)).hasDerivAt_eq_zero hd
    · have hmem := hcompact.sSup_mem hne
      rw [hk, hrange] at hmem
      obtain ⟨s, hs⟩ := hmem
      apply hsingular s k hs
      intro r hr hd
      have hmax : IsMaxOn Δ Set.univ s := by
        intro t _
        rw [hs, ← hk]
        apply le_csSup hcompact.bddAbove
        rw [hrange]
        exact Set.mem_range_self t
      exact (hmax.isLocalMax (by simp)).hasDerivAt_eq_zero hd
  · intro hdeg
    obtain ⟨k, hk⟩ := unipotent_rotation_profile_extremum (φ 1)
      (hsymp 1 ⟨by norm_num, le_rfl⟩) hdeg Δ hcont
      (fun s => by
        obtain ⟨r, hr, hvec, _⟩ := hpolar s
        exact ⟨r, hr, hvec⟩)
    refine ⟨k, ?_⟩
    rw [hrange]
    exact hk.elim (fun h => Or.inl h.csInf_eq) (fun h => Or.inr h.csSup_eq)
