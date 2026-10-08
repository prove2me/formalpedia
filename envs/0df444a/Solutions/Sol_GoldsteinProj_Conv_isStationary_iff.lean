-- Prove2me | solution 1 for GoldsteinProj.Conv.isStationary_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:27:14.428993+00:00
-- url     : https://prove2.me/submissions/ef96a132-95f5-4a30-8f4a-43ceab4459bd

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

set_option autoImplicit false

open Filter Topology RealInnerProductSpace

open GoldsteinProj.Conv in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hfcvx : ConvexOn ℝ C f) (z : H) (hz : z ∈ C)
    (hfdiff : DifferentiableAt ℝ f z) :
    IsStationary f C P z ↔ ∀ y ∈ C, fderiv ℝ f z z ≤ fderiv ℝ f z y := by
  have hgi : ∀ v, ⟪gradient f z, v⟫ = fderiv ℝ f z v := fun v => by
    simp only [gradient]; exact InnerProductSpace.toDual_symm_apply
  constructor
  · rintro ⟨-, hst⟩ y hy
    have h1 := hst 1 one_pos
    rw [one_smul] at h1
    have hmin : ‖(z - gradient f z) - z‖ = ⨅ w : C, ‖(z - gradient f z) - w‖ := by
      have : Nonempty C := ⟨⟨z, hz⟩⟩
      apply le_antisymm
      · apply le_ciInf
        rintro ⟨w, hw⟩
        have := (hP (z - gradient f z)).2 w hw
        rwa [h1] at this
      · have hb : BddBelow (Set.range fun w : C => ‖(z - gradient f z) - (w : H)‖) :=
          ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        exact ciInf_le hb ⟨z, hz⟩
    have h0 := (norm_eq_iInf_iff_real_inner_le_zero hCv hz).1 hmin y hy
    have h2 : ⟪gradient f z, y - z⟫ = fderiv ℝ f z y - fderiv ℝ f z z := by
      rw [hgi, map_sub]
    have h3 : ⟪(z - gradient f z) - z, y - z⟫ = -⟪gradient f z, y - z⟫ := by
      rw [show (z - gradient f z) - z = -gradient f z by abel, inner_neg_left]
    linarith
  · intro hmin
    refine ⟨hz, fun ρ hρ => ?_⟩
    obtain ⟨hPx, hcl⟩ := hP (z - ρ • gradient f z)
    have hle := hcl z hz
    have hinner : 0 ≤ ⟪gradient f z, P (z - ρ • gradient f z) - z⟫ := by
      rw [hgi, map_sub]; linarith [hmin _ hPx]
    have e1 : z - ρ • gradient f z - P (z - ρ • gradient f z)
        = -(ρ • gradient f z + (P (z - ρ • gradient f z) - z)) := by abel
    have e2 : z - ρ • gradient f z - z = -(ρ • gradient f z) := by abel
    rw [e1, e2, norm_neg, norm_neg] at hle
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [norm_add_sq_real, real_inner_smul_left] at hsq
    have hm := mul_nonneg hρ.le hinner
    have h4 : ‖P (z - ρ • gradient f z) - z‖ ^ 2 ≤ 0 := by linarith
    have h5 : ‖P (z - ρ • gradient f z) - z‖ = 0 := by
      nlinarith [norm_nonneg (P (z - ρ • gradient f z) - z)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h5)
