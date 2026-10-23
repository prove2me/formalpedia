-- Prove2me | solution 1 for JHolomorphic.eventuallyEq_of_iteratedFDeriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T14:47:32.387137+00:00
-- url     : https://prove2.me/submissions/f0092cea-3c1e-4bfb-8d91-17ab10f5f320

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_exists_finrank_eq_two_mul_of_comp_eq_neg_id
import Theorems.Thm_JHolomorphic_eventuallyEq_zero_of_forall_norm_le_pow
import Theorems.Thm_JHolomorphic_exists_norm_sub_le_pow_of_iteratedFDeriv_eq
import Theorems.Thm_JHolomorphic_exists_holomorphic_norm_comparable_of_norm_dbar_le
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations



namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Proposition 2.28. -/
theorem eventuallyEq_of_iteratedFDeriv_eq_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (u v : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u (ball 0 1)) (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (huh : IsJHolomorphicOn J (ball 0 1) u) (hvh : IsJHolomorphicOn J (ball 0 1) v)
    (hum : Set.MapsTo u (ball 0 1) O) (hvm : Set.MapsTo v (ball 0 1) O)
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    u =ᶠ[𝓝 0] v := by
  have h00 : u 0 = v 0 := by
    have := congrArg (fun T => T (0 : Fin 0 → ℂ)) (hD 0)
    simpa using this
  have h0D : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hD1 : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  have hx0 : u 0 ∈ O := hum h0D
  obtain ⟨n, hn⟩ := exists_finrank_eq_two_mul_of_comp_eq_neg_id (J (u 0)) (hJ.2.2 _ hx0)
  -- local Lipschitz bound for `J` at `u 0`
  have hJ1 : ContDiffAt ℝ 1 J (u 0) :=
    (hJ.2.1.contDiffAt (hJ.1.mem_nhds hx0)).of_le (by simp)
  obtain ⟨K, t, ht, hLip⟩ := hJ1.exists_lipschitzOnWith
  have hut : u ⁻¹' t ∈ 𝓝 (0 : ℂ) :=
    (hu.continuousOn.continuousAt hD1).preimage_mem_nhds ht
  have hvt : v ⁻¹' t ∈ 𝓝 (0 : ℂ) :=
    (hv.continuousOn.continuousAt hD1).preimage_mem_nhds (h00 ▸ ht)
  -- bound on `Dv` near `0`
  have hDv : ContinuousAt (fderiv ℝ v) 0 :=
    (hv.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).continuousAt hD1
  set B := ‖fderiv ℝ v 0‖ + 1
  have hB : ∀ᶠ z in 𝓝 (0 : ℂ), ‖fderiv ℝ v z‖ ≤ B :=
    (hDv.norm.eventually (gt_mem_nhds (lt_add_one ‖fderiv ℝ v 0‖))).mono fun _ h => h.le
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem (inter_mem hut hvt) hB) hD1)
  -- the difference satisfies a linear Cauchy–Riemann inequality
  set h : ℂ → E := fun z => u z - v z with hh_def
  have hhs : ContDiffOn ℝ ∞ h (ball 0 1) := hu.sub hv
  have hJbar : ContDiffOn ℝ ∞ (fun z => J (u z)) (ball 0 1) := hJ.2.1.comp hu hum
  have hJbar2 : ∀ z ∈ ball (0 : ℂ) 1,
      (J (u z)).comp (J (u z)) = -ContinuousLinearMap.id ℝ E := fun z hz => hJ.2.2 _ (hum hz)
  have hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ h z 1 + J (u z) (fderiv ℝ h z Complex.I)‖ ≤ (K * B) * ‖h z‖ := by
    intro z hz
    obtain ⟨⟨⟨hzu, hzv⟩, hzB⟩, hz1⟩ := hρs hz
    obtain ⟨hud, hu0⟩ := huh z hz1
    obtain ⟨hvd, hv0⟩ := hvh z hz1
    have hfd : fderiv ℝ h z = fderiv ℝ u z - fderiv ℝ v z := fderiv_fun_sub hud hvd
    have hkey : fderiv ℝ h z 1 + J (u z) (fderiv ℝ h z Complex.I) =
        -((J (u z) - J (v z)) (fderiv ℝ v z Complex.I)) := by
      unfold dbarJ at hu0 hv0
      rw [hfd]
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      have e1 : fderiv ℝ u z 1 = -(J (u z) (fderiv ℝ u z Complex.I)) :=
        eq_neg_of_add_eq_zero_left hu0
      have e2 : fderiv ℝ v z 1 = -(J (v z) (fderiv ℝ v z Complex.I)) :=
        eq_neg_of_add_eq_zero_left hv0
      rw [e1, e2]
      abel
    rw [hkey, norm_neg]
    have hI : ‖fderiv ℝ v z Complex.I‖ ≤ B := by
      refine ((fderiv ℝ v z).le_opNorm _).trans ?_
      rw [Complex.norm_I, mul_one]
      exact hzB
    have hL : ‖J (u z) - J (v z)‖ ≤ K * ‖h z‖ := hLip.norm_sub_le hzu hzv
    calc _ ≤ ‖J (u z) - J (v z)‖ * ‖fderiv ℝ v z Complex.I‖ := (J (u z) - J (v z)).le_opNorm _
      _ ≤ (K * ‖h z‖) * B := mul_le_mul hL hI (norm_nonneg _) (by positivity)
      _ = (K * B) * ‖h z‖ := by ring
  obtain ⟨ε, hε, C, f, hf, hcomp⟩ :=
    exists_holomorphic_norm_comparable_of_norm_dbar_le n hn (fun z => J (u z)) hJbar hJbar2 h hhs
      ρ (K * B) hρ hM
  have hT := exists_norm_sub_le_pow_of_iteratedFDeriv_eq 1 one_pos u v hu hv hD
  have hf0 : f =ᶠ[𝓝 0] 0 := by
    refine eventuallyEq_zero_of_forall_norm_le_pow ε hε f hf fun N => ?_
    obtain ⟨C', δ, hδ, hC'⟩ := hT N
    refine ⟨max C 0 * C', min δ ε, lt_min hδ hε, fun z hz => ?_⟩
    have hzδ : z ∈ ball (0 : ℂ) δ := ball_subset_ball (min_le_left _ _) hz
    have hzε : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_right _ _) hz
    calc ‖f z‖ ≤ C * ‖h z‖ := (hcomp z hzε).1
      _ ≤ max C 0 * ‖h z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max C 0 * (C' * ‖z‖ ^ N) := mul_le_mul_of_nonneg_left (hC' z hzδ) (le_max_right _ _)
      _ = _ := by ring
  filter_upwards [hf0, ball_mem_nhds (0 : ℂ) hε] with z hz hzε
  have := (hcomp z hzε).2
  rw [hz, Pi.zero_apply, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (u v : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u (ball 0 1)) (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (huh : IsJHolomorphicOn J (ball 0 1) u) (hvh : IsJHolomorphicOn J (ball 0 1) v)
    (hum : Set.MapsTo u (ball 0 1) O) (hvm : Set.MapsTo v (ball 0 1) O)
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    u =ᶠ[𝓝 0] v :=
  eventuallyEq_of_iteratedFDeriv_eq_aux J O hJ u v hu hv huh hvh hum hvm hD
