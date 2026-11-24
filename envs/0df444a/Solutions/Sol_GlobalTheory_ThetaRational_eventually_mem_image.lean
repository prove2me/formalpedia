-- Prove2me | solution 1 for GlobalTheory.ThetaRational.eventually_mem_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:03.568088+00:00
-- url     : https://prove2.me/submissions/48e15e96-56a4-411f-912a-4b50334c1812

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_exists_rep
import Theorems.Thm_GlobalTheory_ThetaRational_exists_lower_bound
import Theorems.Thm_GlobalTheory_ThetaRational_exists_transl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}
omit [FiniteDimensional ℂ W]
namespace GlobalTheory.ThetaRational
theorem _root_.solution (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    {e : ℂ × V} (he : e.1 • θ e.2 ≠ 0) {U : Set (ℂ × V)} (hU : U ∈ 𝓝 e) :
    ∀ᶠ y in 𝓝 (e.1 • θ e.2), ∀ x : ℂ × V, x.1 • θ x.2 = y → ∃ x' ∈ U, x'.1 • θ x'.2 = y := by
  obtain ⟨ε, hε, hεK⟩ := exists_lower_bound hK hθ hN
  set Θ : ℂ × V → W := fun x => x.1 • θ x.2 with hΘ
  have hΘc : Continuous Θ := by rw [hΘ]; fun_prop
  set S : Set (ℂ × V) := {x | ∃ x' ∈ U, Θ x' = Θ x} with hSdef
  set M : Set (ℂ × V) := Metric.closedBall (0 : ℂ) ((‖Θ e‖ + 1) / ε) ×ˢ K with hM
  have hMc : IsCompact M := (isCompact_closedBall _ _).prod hK
  have hC : IsClosed (Θ '' (M \ interior S)) := ((hMc.diff isOpen_interior).image hΘc).isClosed
  have hne : Θ e ∈ (Θ '' (M \ interior S))ᶜ := by
    rintro ⟨e', ⟨-, h1⟩, h2⟩
    apply h1
    obtain ⟨T, hTc, hTe, hT⟩ := exists_transl hN hL hS he h2
    rw [mem_interior_iff_mem_nhds]
    have : T ⁻¹' U ∈ 𝓝 e' := hTc.continuousAt.preimage_mem_nhds (by rwa [hTe])
    filter_upwards [this] with x hx using ⟨T x, hx, (hT x).1⟩
  have h5 : ∀ᶠ y in 𝓝 (Θ e), ‖y‖ < ‖Θ e‖ + 1 :=
    continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [hC.isOpen_compl.mem_nhds hne, h5] with y hy hy' x hx
  obtain ⟨x', hx', h1, -⟩ := exists_rep hP hL x
  have h2 : Θ x' = y := h1.trans hx
  have h3 : x' ∈ M := by
    refine ⟨?_, hx'⟩
    rw [mem_closedBall_zero_iff, le_div_iff₀ hε]
    refine le_trans ?_ hy'.le
    rw [← h2, hΘ]
    simp only [norm_smul]
    gcongr
    exact hεK _ hx'
  have h4 : x' ∈ interior S := by
    by_contra h
    exact hy ⟨x', ⟨h3, h⟩, h2⟩
  obtain ⟨x'', h6, h7⟩ := interior_subset h4
  exact ⟨x'', h6, h7.trans h2⟩
end GlobalTheory.ThetaRational
