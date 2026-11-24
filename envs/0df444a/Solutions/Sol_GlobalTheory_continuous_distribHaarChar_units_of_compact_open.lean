-- Prove2me | solution 1 for GlobalTheory.continuous_distribHaarChar_units_of_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:03.025841+00:00
-- url     : https://prove2.me/submissions/cade6800-745a-4d43-a730-196489be35e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSn : S.Nonempty) : Continuous (fun u : Rˣ => distribHaarChar R u) := by
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hSc hSo subset_rfl
  have h0 : μ S ≠ 0 := hSo.measure_ne_zero μ hSn
  have ht : μ S ≠ ⊤ := hSc.measure_lt_top.ne
  have hle : ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u ≤ 1 := by
    intro u hu
    have h1 : μ (u • S) ≤ μ S := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u S] at h1
    have h2 : ((distribHaarChar R u : NNReal) : ENNReal) * μ S ≤ 1 * μ S := by simpa using h1
    have h3 := (ENNReal.mul_le_mul_iff_left h0 ht).1 h2
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
    Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
  have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
    Units.continuous_coe_inv.continuousAt.eventually
      (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
  have e3 : (fun _ : Rˣ => (1 : NNReal)) =ᶠ[𝓝 1] (distribHaarChar R : Rˣ →* NNReal) := by
    filter_upwards [e1, e2] with u h1 h2
    have a1 := hle u h1
    have a2 := hle u⁻¹ h2
    have a3 : distribHaarChar R u * distribHaarChar R u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    refine le_antisymm ?_ a1
    calc (1 : NNReal) = distribHaarChar R u * distribHaarChar R u⁻¹ := a3.symm
      _ ≤ distribHaarChar R u * 1 := by gcongr
      _ = _ := mul_one _
  exact continuousAt_const.congr e3
end GlobalTheory
