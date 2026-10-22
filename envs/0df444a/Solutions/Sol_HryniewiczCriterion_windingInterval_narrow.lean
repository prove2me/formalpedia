-- Prove2me | solution 1 for HryniewiczCriterion.windingInterval_narrow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T22:17:15.926972+00:00
-- url     : https://prove2.me/submissions/2d189180-c6fa-4233-9493-9c35e123a347

import Theorems.Thm_BirkhoffGlobalSection_plane_family_winding_interval
import Theorems.Thm_BirkhoffGlobalSection_area_preserving_polar_winding_width
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Theorems.Thm_BirkhoffGlobalSection_plane_family_normalized_polar_lift
import Theorems.Thm_BirkhoffGlobalSection_continuous_angle_increment_unique
import Theorems.Thm_BirkhoffGlobalSection_plane_positive_polar_unique
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open HryniewiczCriterion Set Filter Topology
open scoped ContDiff
set_option maxHeartbeats 800000


theorem solution (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    ∃ a b : ℝ, a ≤ b ∧ windingInterval φ = Set.Icc a b ∧ b - a < 1 / 2 := by
  let clip : ℝ → ℝ := fun t => (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ)
  have hclip : Continuous clip := continuous_subtype_val.comp continuous_projIcc
  have hclipmem (t : ℝ) : clip t ∈ Icc (0 : ℝ) 1 :=
    (Set.projIcc (0 : ℝ) 1 (by norm_num) t).property
  have hclipeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clip t = t := by
    simp only [clip, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht]
  have hclip0 : clip 0 = 0 := hclipeq 0 ⟨le_rfl, by norm_num⟩
  have hclip1 : clip 1 = 1 := hclipeq 1 ⟨by norm_num, le_rfl⟩
  have hφclip : Continuous (fun t => φ (clip t)) :=
    hφ.continuousOn.comp_continuous hclip hclipmem
  let v : ℝ × ℝ → (Fin 2 → ℝ) :=
    fun x => (φ (clip x.1)).mulVec (rotationVector x.2)
  have hv : Continuous v := by
    apply continuous_pi
    intro i
    simp only [v, rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ((((continuous_apply 0).comp ((continuous_apply i).comp hφclip)).comp continuous_fst).mul
      (Real.continuous_cos.comp continuous_snd)).add
      ((((continuous_apply 1).comp ((continuous_apply i).comp hφclip)).comp continuous_fst).mul
      (Real.continuous_sin.comp continuous_snd))
  have hrotne (s : ℝ) : rotationVector s ≠ 0 := by
    intro he
    have hc := congrFun he 0
    have hs := congrFun he 1
    simp only [rotationVector, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at hc hs
    have h := Real.cos_sq_add_sin_sq s
    rw [hc, hs] at h
    norm_num at h
  have hne (x : ℝ × ℝ) : v x ≠ 0 := by
    intro he
    apply hrotne x.2
    exact Matrix.eq_zero_of_mulVec_eq_zero
      (by rw [hsymp (clip x.1) (hclipmem x.1)]; norm_num) he
  have hzero (s : ℝ) : v (0, s) = ![Real.cos s, Real.sin s] := by
    simp only [v, hclip0, h0, Matrix.one_mulVec, rotationVector]
  obtain ⟨ρ, θ, hρ, hθ, hp, hθ0, hpol⟩ :=
    BirkhoffGlobalSection.plane_family_normalized_polar_lift v hv hne hzero
  have hvpol (x : ℝ × ℝ) : v x = ρ x • rotationVector (θ x) := by
    simpa only [rotationVector, Matrix.smul_vec2, smul_eq_mul] using hpol x
  let Δ : ℝ → ℝ := fun s => (θ (1, s) - s) / (2 * Real.pi)
  have hΔ : Continuous Δ :=
    ((hθ.comp (continuous_const.prodMk continuous_id)).sub continuous_id).div_const _
  have hangle (s : ℝ) : IsAngleLift φ s (fun t => θ (t, s)) := by
    refine ⟨(hθ.comp (continuous_id.prodMk continuous_const)).continuousOn, hθ0 s, ?_⟩
    intro t ht
    refine ⟨ρ (t, s), hp _, ?_⟩
    simpa only [v, hclipeq t ht] using hvpol (t, s)
  have himage : windingInterval φ = Δ '' Icc (0 : ℝ) (2 * Real.pi) := by
    ext d
    constructor
    · rintro ⟨s, hs, ψ, hψ, hd⟩
      have hψclip : Continuous (fun t => ψ (clip t)) :=
        hψ.1.comp_continuous hclip hclipmem
      have hdir (t : ℝ) :
          Real.cos (ψ (clip t)) = Real.cos (θ (t, s)) ∧
          Real.sin (ψ (clip t)) = Real.sin (θ (t, s)) := by
        obtain ⟨r, hr, he⟩ := hψ.2.2 (clip t) (hclipmem t)
        have he' : v (t, s) = ![r * Real.cos (ψ (clip t)), r * Real.sin (ψ (clip t))] := by
          simpa only [v, rotationVector, Matrix.smul_vec2, smul_eq_mul] using he
        exact (BirkhoffGlobalSection.plane_positive_polar_unique (v (t, s))
          r (ρ (t, s)) (ψ (clip t)) (θ (t, s)) hr (hp _) he' (hpol _)).2
      have hin := BirkhoffGlobalSection.continuous_angle_increment_unique
        (fun t => ψ (clip t)) (fun t => θ (t, s)) hψclip
        (hθ.comp (continuous_id.prodMk continuous_const))
        (fun t => (hdir t).1) (fun t => (hdir t).2) 1
      rw [hclip1, hclip0, hψ.2.1, hθ0] at hin
      refine ⟨s, hs, ?_⟩
      dsimp [Δ]
      rw [hd, hin]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, (fun t => θ (t, s)), hangle s, rfl⟩
  obtain ⟨a, b, hab, hi, ha, hb⟩ :=
    BirkhoffGlobalSection.plane_family_winding_interval θ hθ 1
  have hw : windingInterval φ = Icc a b := himage.trans hi
  refine ⟨a, b, hab, hw, ?_⟩
  apply BirkhoffGlobalSection.area_preserving_polar_winding_width
    (fun t p => (φ (clip t)).mulVec p) ρ θ hθ hp hθ0
    (fun t s => hpol (t, s)) ?_ ?_ 1 a b hab hi
  · intro t p r
    have hd := hsymp (clip t) (hclipmem t)
    rw [Matrix.det_fin_two] at hd
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    calc
      _ = ((φ (clip t)) 0 0 * (φ (clip t)) 1 1 -
        (φ (clip t)) 0 1 * (φ (clip t)) 1 0) * (p 0 * r 1 - p 1 * r 0) := by ring
      _ = _ := by rw [hd]; ring
  · intro t p
    exact Matrix.mulVec_neg _ _
