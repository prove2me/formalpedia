-- Prove2me | solution 1 for GlobalTheory.exists_finite_measure_cover_of_drift_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:24.863961+00:00
-- url     : https://prove2.me/submissions/1a5538b2-c9b1-487b-90fd-8f13765d40a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasureUnivLeTwoMulSublevelOfDrift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStrictMeasurableFundamentalSetOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HaarMapMulRightOfConjInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FundamentalSetLintegralMulRightAndMeasureLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteCovolumeOfDriftFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverOfDriftFunction
import Theorems.Thm_GlobalTheory_exists_strict_measurable_fundamental_set_of_discrete
import Theorems.Thm_GlobalTheory_finite_covolume_of_drift_function
import Theorems.Thm_GlobalTheory_fundamentalSet_lintegral_mul_right_and_measure_le
import Theorems.Thm_GlobalTheory_haar_map_mul_right_of_conj_inv
import Theorems.Thm_GlobalTheory_measure_univ_le_two_mul_sublevel_of_drift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) :=
  GlobalTheory.finite_covolume_of_drift_function GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift
    GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete GlobalTheory.haar_map_mul_right_of_conj_inv
    GlobalTheory.fundamentalSet_lintegral_mul_right_and_measure_le
end GlobalTheory
