-- Prove2me | solution 1 for JHolomorphic.eq_zero_of_norm_dbar_le_of_eqOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T11:10:21.194802+00:00
-- url     : https://prove2.me/submissions/6ce80360-86ef-45f4-b97b-9862d706961d

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Theorems.Thm_JHolomorphic_exists_finrank_eq_two_mul_of_comp_eq_neg_id
import Theorems.Thm_JHolomorphic_eventuallyEq_zero_of_forall_norm_le_pow
import Theorems.Thm_JHolomorphic_exists_norm_sub_le_pow_of_iteratedFDeriv_eq
import Theorems.Thm_JHolomorphic_exists_holomorphic_norm_comparable_of_norm_dbar_le
import Mathlib.Topology.Connected.Clopen



namespace JHolomorphic

open Metric Filter Topology
open scoped ContDiff

/-- A smooth `h : ℂ → E` satisfying, near every point, `‖∂ₛh + J̄(z) ∂ₜh‖ ≤ M ‖h‖` for a smooth
complex structure `J̄`, and vanishing on a nonempty open set, vanishes identically. -/
theorem eq_zero_of_norm_dbar_le_of_eqOn_zero_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiff ℝ ∞ Jbar)
    (hJbar2 : ∀ z, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiff ℝ ∞ h)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (h0 : ∀ z ∈ U, h z = 0) :
    ∀ z, h z = 0 := by
  obtain ⟨n, hn⟩ := exists_finrank_eq_two_mul_of_comp_eq_neg_id (Jbar 0) (hJbar2 0)
  -- local step: an infinite-order zero is a local zero
  have hloc : ∀ z₀ : ℂ, (∀ m : ℕ, iteratedFDeriv ℝ m h z₀ = 0) → h =ᶠ[𝓝 z₀] 0 := by
    intro z₀ hD
    obtain ⟨ρ, hρ, M, hMb⟩ := hM z₀
    set g : ℂ → E := fun z => h (z₀ + z) with hg
    set Jg : ℂ → E →L[ℝ] E := fun z => Jbar (z₀ + z) with hJg
    have hgs : ContDiff ℝ ∞ g := hh.comp (contDiff_const.add contDiff_id)
    have hJgs : ContDiff ℝ ∞ Jg := hJbar.comp (contDiff_const.add contDiff_id)
    have hfd : ∀ z, fderiv ℝ g z = fderiv ℝ h (z₀ + z) := fun z => fderiv_comp_add_left z₀
    have hMg : ∀ z ∈ ball (0 : ℂ) ρ,
        ‖fderiv ℝ g z 1 + Jg z (fderiv ℝ g z Complex.I)‖ ≤ M * ‖g z‖ := by
      intro z hz
      rw [hfd]
      apply hMb
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right]
      exact hz
    obtain ⟨ε, hε, C, f, hf, hcomp⟩ :=
      exists_holomorphic_norm_comparable_of_norm_dbar_le n hn Jg hJgs.contDiffOn
        (fun z _ => hJbar2 _) g hgs.contDiffOn ρ M hρ hMg
    have hDg : ∀ m : ℕ, iteratedFDeriv ℝ m g 0 = iteratedFDeriv ℝ m (fun _ : ℂ => (0 : E)) 0 := by
      intro m
      rw [hg, iteratedFDeriv_comp_add_left, add_zero, hD m]
      exact (congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := ℂ) (F := E) (n := m)) 0).symm
    have hT := exists_norm_sub_le_pow_of_iteratedFDeriv_eq 1 one_pos g (fun _ => (0 : E))
      hgs.contDiffOn contDiffOn_const hDg
    have hf0 : f =ᶠ[𝓝 0] 0 := by
      refine eventuallyEq_zero_of_forall_norm_le_pow ε hε f hf fun N => ?_
      obtain ⟨C', δ, hδ, hC'⟩ := hT N
      refine ⟨max C 0 * C', min δ ε, lt_min hδ hε, fun z hz => ?_⟩
      have hzδ : z ∈ ball (0 : ℂ) δ := ball_subset_ball (min_le_left _ _) hz
      have hzε : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_right _ _) hz
      have h1 := hC' z hzδ
      rw [sub_zero] at h1
      calc ‖f z‖ ≤ C * ‖g z‖ := (hcomp z hzε).1
        _ ≤ max C 0 * ‖g z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C 0 * (C' * ‖z‖ ^ N) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
        _ = _ := by ring
    have hg0 : g =ᶠ[𝓝 0] 0 := by
      filter_upwards [hf0, ball_mem_nhds (0 : ℂ) hε] with z hz hzε
      have := (hcomp z hzε).2
      rw [hz, Pi.zero_apply, norm_zero, mul_zero] at this
      exact norm_le_zero_iff.1 this
    -- transport back
    have hcont : Continuous fun z : ℂ => z - z₀ := continuous_id.sub continuous_const
    have hmem := hcont.continuousAt.preimage_mem_nhds (x := z₀) (by rw [sub_self]; exact hg0)
    filter_upwards [hmem] with z hz
    have : g (z - z₀) = 0 := hz
    simpa [hg] using this
  -- the infinite-order zero set is clopen
  set A : Set ℂ := {z | ∀ m : ℕ, iteratedFDeriv ℝ m h z = 0} with hA
  have hAclosed : IsClosed A := by
    have : A = ⋂ m : ℕ, (fun z => iteratedFDeriv ℝ m h z) ⁻¹' {0} := by
      ext z; simp [hA]
    rw [this]
    exact isClosed_iInter fun m =>
      isClosed_singleton.preimage (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have h1 := hloc z hz
    have h2 : ∀ᶠ y in 𝓝 z, h =ᶠ[𝓝 y] 0 := h1.eventually_nhds
    filter_upwards [h2] with y hy m
    have := (hy.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
    rw [this]
    exact congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := ℂ) (F := E) (n := m)) y
  obtain ⟨z₁, hz₁⟩ := hne
  have hA1 : z₁ ∈ A := by
    intro m
    have hev : h =ᶠ[𝓝 z₁] 0 := by
      filter_upwards [hU.mem_nhds hz₁] with y hy using h0 y hy
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := ℂ) (F := E) (n := m)) z₁
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ ⟨z₁, hA1⟩
  intro z
  have hz : z ∈ A := hAuniv ▸ Set.mem_univ z
  have := hz 0
  have := congrArg (fun T => T (0 : Fin 0 → ℂ)) this
  simpa using this

end JHolomorphic

open JHolomorphic

open Metric Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiff ℝ ∞ Jbar)
    (hJbar2 : ∀ z, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiff ℝ ∞ h)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (h0 : ∀ z ∈ U, h z = 0) :
    ∀ z, h z = 0 :=
  eq_zero_of_norm_dbar_le_of_eqOn_zero_aux Jbar hJbar hJbar2 h hh hM U hU hne h0
