-- Prove2me | solution 1 for GlobalTheory.PeriodicWeierstrass.exists_eq_of_cube_mul_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:32.259906+00:00
-- url     : https://prove2.me/submissions/b431c876-f58c-48d8-b71d-eb102fb9c2c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsConstOfSqMulTendstoZero
import Theorems.Thm_GlobalTheory_PeriodicWeierstrass_exists_eq_of_sq_mul_tendsto
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter PeriodPair
open scoped Topology
noncomputable section
namespace GlobalTheory
namespace PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair in
open scoped Topology in
private lemma exists_tendsto_pow_mul_of_tendsto_pow_succ_mul_zero {h : ℂ → ℂ} (k : ℕ)
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ h z)
    (h2 : Tendsto (fun z ↦ z ^ (k + 1) * h z) (𝓝[≠] 0) (𝓝 0)) :
    ∃ r, Tendsto (fun z ↦ z ^ k * h z) (𝓝[≠] 0) (𝓝 r) := by
  set u := Function.update (fun z ↦ z ^ (k + 1) * h z) 0 0 with hu
  have hcont : ContinuousAt u 0 := by
    rw [hu, continuousAt_update_same]; exact h2
  have hdu : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ u z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hz hz0
    refine (((differentiableAt_id.pow (k + 1)).mul hz)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
    simp [hu, Function.update_of_ne (show w ≠ 0 from hw)]
  have hA : AnalyticAt ℂ u 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdu hcont
  refine ⟨deriv u 0, ?_⟩
  refine hA.differentiableAt.hasDerivAt.tendsto_slope_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  simp [hu, Function.update_of_ne ht, pow_succ]
  field_simp
open Filter PeriodPair in
open scoped Topology in
private lemma tendsto_pow_three_mul_derivWeierstrassP (L : PeriodPair) :
    Tendsto (fun z ↦ z ^ 3 * ℘'[L] z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hA : AnalyticAt ℂ ℘'[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_derivWeierstrassPExcept 0 0 (by simp)
  have hc : Tendsto (fun z ↦ z ^ 3 * ℘'[L - (0 : ℂ)] z - 2) (𝓝[≠] 0)
      (𝓝 (0 ^ 3 * ℘'[L - (0:ℂ)] 0 - 2)) :=
    (((continuous_pow 3).continuousAt.mul hA.continuousAt).sub continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_sub] at hc
  refine hc.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz' : z ≠ 0 := hz
  have := L.derivWeierstrassPExcept_def ⟨0, h0⟩ z
  simp only [sub_zero] at this
  rw [this]
  field_simp
  ring
end PeriodicWeierstrass
end GlobalTheory
end
end

set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory
open GlobalTheory.PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair
open scoped Topology
namespace GlobalTheory.PeriodicWeierstrass
namespace _root_.GlobalTheory.PeriodicWeierstrass
theorem _root_.solution (L : PeriodPair) {g : ℂ → ℂ}
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z) (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z)
    (h : Tendsto (fun z ↦ z ^ 3 * g z) (𝓝[≠] 0) (𝓝 (-2))) :
    ∃ b k, ∀ z ∉ L.lattice, g z = ℘'[L] z + b * ℘[L] z + k := by
  set f₀ : ℂ → ℂ := fun z => g z - ℘'[L] z with hf₀
  have hd₀ : ∀ z ∉ L.lattice, DifferentiableAt ℂ f₀ z := fun z hz =>
    (hd z hz).sub (_root_.GlobalTheory.hasDerivAt_derivWeierstrassP L hz).differentiableAt
  have hp₀ : ∀ z, ∀ l ∈ L.lattice, f₀ (z + l) = f₀ z := fun z l hl => by
    simp only [hf₀, hp z l hl, L.derivWeierstrassP_add_coe z ⟨l, hl⟩]
  have h3 : Tendsto (fun z => z ^ (2 + 1) * f₀ z) (𝓝[≠] 0) (𝓝 0) := by
    have := h.sub (tendsto_pow_three_mul_derivWeierstrassP L)
    rw [sub_self] at this
    refine this.congr' (Eventually.of_forall fun z => ?_)
    simp only [hf₀]
    ring
  obtain ⟨s, hs⟩ := exists_tendsto_pow_mul_of_tendsto_pow_succ_mul_zero 2
    ((_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0).mono fun z hz => hd₀ z hz) h3
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.PeriodicWeierstrass.exists_eq_of_sq_mul_tendsto L hd₀ hp₀ hs
  refine ⟨s, k, fun z hz => ?_⟩
  have := hk z hz
  simp only [hf₀] at this
  linear_combination this
end _root_.GlobalTheory.PeriodicWeierstrass
end GlobalTheory.PeriodicWeierstrass
