-- Prove2me | solution 1 for HryniewiczCriterion.winding_endpoint_profile
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T20:50:34.35406+00:00
-- url     : https://prove2.me/submissions/2d108e0c-0c5e-4ef7-b474-46da73c54f98

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Theorems.Thm_HryniewiczCriterion_positive_polar_angle_derivative
import Theorems.Thm_BirkhoffGlobalSection_plane_family_normalized_polar_lift
import Theorems.Thm_BirkhoffGlobalSection_normalized_plane_family_angle_shift
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

theorem solution
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    ∃ Δ : ℝ → ℝ, Continuous Δ ∧
      windingInterval φ = Δ '' Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      windingInterval φ = Set.range Δ ∧
      ∀ s : ℝ, ∃ r : ℝ, 0 < r ∧
        (φ 1).mulVec (rotationVector s) =
          r • rotationVector (s + 2 * Real.pi * Δ s) ∧
        HasDerivAt Δ ((1 / r ^ 2 - 1) / (2 * Real.pi)) s := by
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
  have hperiodv (t s : ℝ) : v (t, s + 2 * Real.pi) = v (t, s) := by
    have hr : rotationVector (s + 2 * Real.pi) = rotationVector s := by
      ext i
      fin_cases i <;> simp [rotationVector]
    simp only [v, hr]
  have hshift := BirkhoffGlobalSection.normalized_plane_family_angle_shift
    v ρ θ hθ hp hθ0 hpol (2 * Real.pi) hperiodv
  have hperiod : Function.Periodic Δ (2 * Real.pi) := by
    intro s
    dsimp [Δ]
    rw [hshift]
    congr 1
    ring
  have hrange : windingInterval φ = Set.range Δ := by
    rw [himage]
    apply Set.Subset.antisymm
    · rintro _ ⟨s, _, rfl⟩
      exact Set.mem_range_self s
    · rintro _ ⟨s, rfl⟩
      let n : ℤ := Int.floor (s / (2 * Real.pi))
      let u := s - n * (2 * Real.pi)
      have hu0 : 0 ≤ u := Int.sub_floor_div_mul_nonneg s (by positivity)
      have hupi : u < 2 * Real.pi := Int.sub_floor_div_mul_lt s (by positivity)
      have he : Δ u = Δ s := hperiod.sub_int_mul_eq n
      exact ⟨u, ⟨hu0, hupi.le⟩, he⟩
  refine ⟨Δ, hΔ, himage, hrange, ?_⟩
  intro s
  refine ⟨ρ (1, s), hp _, ?_, ?_⟩
  · have he : s + 2 * Real.pi * Δ s = θ (1, s) := by
      dsimp [Δ]
      field_simp
      ring
    rw [he]
    simpa only [v, hclip1] using hvpol (1, s)
  · have hθend : HasDerivAt (fun u => θ (1, u)) (1 / ρ (1, s)^2) s := by
      apply HryniewiczCriterion.positive_polar_angle_derivative (φ 1)
        (hsymp 1 ⟨by norm_num, le_rfl⟩) _ (hθ.comp (continuous_const.prodMk continuous_id))
        (fun u => ⟨ρ (1, u), hp _, by convert! hvpol (1, u) using 1; simp only [v, hclip1]⟩)
        s (ρ (1, s)) (hp _)
      convert! hvpol (1, s) using 1; simp only [v, hclip1]
    exact (hθend.sub (hasDerivAt_id s)).div_const (2 * Real.pi)
