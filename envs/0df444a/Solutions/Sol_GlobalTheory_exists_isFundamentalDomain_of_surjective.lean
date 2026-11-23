-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:49.66199+00:00
-- url     : https://prove2.me/submissions/762095b0-d217-4985-86df-fb4e6e4e2d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_isFundamentalDomain
import Theorems.Thm_GlobalTheory_measure_fixed_eq_zero_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_quotMeasure_univ_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_map_restrict_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measurePreserving_mk
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_univ
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measure_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_lintegral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integrable_quotMeasure_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_image_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_sigmaFinite_quotMeasure
import Theorems.Thm_GlobalTheory_quotMeasure_univ_eq_covolume
import Theorems.Thm_GlobalTheory_lintegral_eq_lintegral_quotMeasure_tsum
import Theorems.Thm_GlobalTheory_exists_measurableSet_orbitSection
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_free
import Theorems.Thm_GlobalTheory_exists_isAEOrbitSection
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_ae_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}
namespace GlobalTheory
theorem _root_.solution [ProperlyDiscontinuousSMul G X] {Q : Type*}
    [Group Q] [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hact : ∀ g (x : X), φ g • x = g • x) (μ : Measure X)
    (hfree : ∀ g : G, φ g ≠ 1 → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain Q D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  refine ⟨D, hD, hc, hu, isFundamentalDomain_of_orbitSection hD.nullMeasurableSet
    (Eventually.of_forall fun x => ?_) (fun x hx q hq => ?_) fun q hq => ?_⟩
  · obtain ⟨g, hg⟩ := hc x
    exact ⟨φ g, by rwa [hact]⟩
  · obtain ⟨g, rfl⟩ := hφ q
    rw [hact] at hq ⊢
    exact hu x hx g hq
  · obtain ⟨g, rfl⟩ := hφ q
    simpa only [hact] using hfree g hq
end GlobalTheory
