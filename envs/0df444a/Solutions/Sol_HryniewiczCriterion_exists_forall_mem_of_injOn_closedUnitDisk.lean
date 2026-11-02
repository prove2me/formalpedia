-- Prove2me | solution 1 for HryniewiczCriterion.exists_forall_mem_of_injOn_closedUnitDisk
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:15:53.725765+00:00
-- url     : https://prove2.me/submissions/2a39bc23-73a9-4927-9c9c-d57a59ddecb1

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace

open HryniewiczCriterion
open scoped ContDiff Topology
open Filter

namespace HryniewiczCriterion

lemma rb1_isClosed_closedUnitDisk : IsClosed closedUnitDisk :=
  isClosed_le (by fun_prop) continuous_const

lemma rb1_isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (by fun_prop) continuous_const

lemma rb1_isCompact_closedUnitDisk : IsCompact closedUnitDisk := by
  refine Metric.isCompact_of_isClosed_isBounded rb1_isClosed_closedUnitDisk ?_
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 1)).subset ?_
  intro u hu
  have hu' : u 0 ^ 2 + u 1 ^ 2 ≤ 1 := hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

lemma rb1_openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := fun u hu =>
  le_of_lt (show u 0 ^ 2 + u 1 ^ 2 < 1 from hu)

/-- Every unit vector is `(cos 2πt, sin 2πt)`. -/
lemma rb1_cos_sin (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : ℝ, Real.cos (2 * Real.pi * t) = a ∧ Real.sin (2 * Real.pi * t) = b := by
  set z : ℂ := ⟨a, b⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [z, ← sq, h]
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩
  · rw [mul_div_cancel₀ _ (by positivity), Complex.cos_arg hz, hn, div_one]
  · rw [mul_div_cancel₀ _ (by positivity), Complex.sin_arg, hn, div_one]

/-- A point of the closed disk off the open disk is a circle point. -/
lemma rb1_exists_circlePoint {v : Plane} (hv : v ∈ closedUnitDisk) (hv' : v ∉ openUnitDisk) :
    ∃ t, v = circlePoint t := by
  have h1 : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := hv
  have h2 : ¬ v 0 ^ 2 + v 1 ^ 2 < 1 := hv'
  obtain ⟨t, ht1, ht2⟩ := rb1_cos_sin (v 0) (v 1) (by linarith [not_lt.1 h2])
  refine ⟨t, ?_⟩
  ext j; fin_cases j
  · simp [circlePoint, ht1]
  · simp [circlePoint, ht2]

/-- `dH(x)(X_H(x)) = 0`. -/
lemma rb1_dH_hvf (H : R4 → ℝ) (x : R4) :
    fderiv ℝ H x (hamiltonianVectorField H x) = 0 := by
  set X := hamiltonianVectorField H x
  have hX : X = ∑ i : Fin 4, X i • (Pi.single i (1 : ℝ) : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hX, map_sum]
  simp only [map_smul, smul_eq_mul, Fin.sum_univ_four]
  simp [X, hamiltonianVectorField, partialDeriv]
  ring

lemma rb1_continuous_hvf {H : R4 → ℝ} (hH : ContDiff ℝ ∞ H) :
    Continuous (hamiltonianVectorField H) := by
  have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have hp : ∀ i, Continuous fun x => partialDeriv H x i := fun i =>
    hc.clm_apply continuous_const
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact (hp 1).neg
  · exact hp 0
  · exact (hp 3).neg
  · exact hp 2

end HryniewiczCriterion

namespace HryniewiczCriterion

/-- Uniform recovery of the parameter: for a jointly continuous family `f θ` with `f θ₀`
injective on the closed disk, nearby parameters and nearby image points force nearby
preimages. -/
lemma rb1_recover {f : ℝ → Plane → R4} (hf : Continuous (fun z : ℝ × Plane => f z.1 z.2))
    {θ₀ : ℝ} {v₀ : Plane} (hinj : Set.InjOn (f θ₀) closedUnitDisk) (hv₀ : v₀ ∈ closedUnitDisk)
    {U : Set (ℝ × Plane)} (hU : U ∈ 𝓝 (θ₀, v₀)) :
    ∃ η > 0, ∀ θ v, |θ - θ₀| < η → v ∈ closedUnitDisk → ‖f θ v - f θ₀ v₀‖ < η →
      (θ, v) ∈ U := by
  obtain ⟨V, hVU, hVo, hpV⟩ := mem_nhds_iff.1 hU
  set K : Set (ℝ × Plane) := Set.Icc (θ₀ - 1) (θ₀ + 1) ×ˢ closedUnitDisk
  have hK : IsCompact K := isCompact_Icc.prod rb1_isCompact_closedUnitDisk
  set C := K ∩ Vᶜ
  have hC : IsCompact C := hK.inter_right hVo.isClosed_compl
  set F : ℝ × Plane → ℝ := fun z => |z.1 - θ₀| + ‖f z.1 z.2 - f θ₀ v₀‖
  have hFc : Continuous F := by
    simp only [F]
    exact (continuous_abs.comp (continuous_fst.sub continuous_const)).add
      ((hf.sub continuous_const).norm)
  have hpos : ∀ z ∈ C, 0 < F z := by
    rintro ⟨θ, v⟩ ⟨⟨_, hv⟩, hnV⟩
    by_contra hle
    have h0 : F (θ, v) = 0 := le_antisymm (not_lt.1 hle) (by positivity)
    have ha : |θ - θ₀| = 0 := by
      have := abs_nonneg (θ - θ₀); have := norm_nonneg (f θ v - f θ₀ v₀)
      simp only [F] at h0; linarith
    have hb : ‖f θ v - f θ₀ v₀‖ = 0 := by
      have := abs_nonneg (θ - θ₀); simp only [F] at h0; linarith
    have hθ : θ = θ₀ := by linarith [abs_eq_zero.1 ha]
    subst hθ
    have : v = v₀ := hinj hv hv₀ (sub_eq_zero.1 (norm_eq_zero.1 hb))
    subst this
    exact hnV hpV
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun θ v hθ hv _ => hVU ?_⟩
    by_contra hnV
    have : (θ, v) ∈ C := ⟨⟨⟨by linarith [(abs_lt.1 hθ).1], by linarith [(abs_lt.1 hθ).2]⟩, hv⟩,
      hnV⟩
    rw [hCe] at this; exact this
  · obtain ⟨z₀, hz₀, hmin⟩ := hC.exists_isMinOn hCne hFc.continuousOn
    have hm := hpos z₀ hz₀
    refine ⟨min 1 (F z₀ / 2), lt_min one_pos (by linarith), fun θ v hθ hv hd => hVU ?_⟩
    by_contra hnV
    have hθ1 : |θ - θ₀| < 1 := lt_of_lt_of_le hθ (min_le_left _ _)
    have hmem : (θ, v) ∈ C := ⟨⟨⟨by linarith [(abs_lt.1 hθ1).1], by linarith [(abs_lt.1 hθ1).2]⟩,
      hv⟩, hnV⟩
    have h1 := hmin hmem
    have h2 : F (θ, v) < F z₀ := by
      simp only [F]
      have := min_le_right 1 (F z₀ / 2)
      linarith
    exact absurd h1 (not_le.2 h2)

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {f : ℝ → Plane → R4}
    (hf : Continuous (fun z : ℝ × Plane => f z.1 z.2))
    {θ₀ : ℝ} {v₀ : Plane} (hinj : Set.InjOn (f θ₀) closedUnitDisk) (hv₀ : v₀ ∈ closedUnitDisk)
    {U : Set (ℝ × Plane)} (hU : U ∈ nhds (θ₀, v₀)) :
    ∃ η > 0, ∀ θ v, |θ - θ₀| < η → v ∈ closedUnitDisk → ‖f θ v - f θ₀ v₀‖ < η →
      (θ, v) ∈ U :=
  rb1_recover hf hinj hv₀ hU
